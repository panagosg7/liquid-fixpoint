{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE GADTs                      #-}

-- | This module contains the data types, operations and
--   serialization functions for representing Fixpoint's
--   implication (i.e. subtyping) and well-formedness
--   constraints in Haskell. The actual constraint
--   solving is done by the `fixpoint.native` which
--   is written in Ocaml.

module Language.Fixpoint.Types (
  -- * Symbols
    Symbol
  , anfPrefix, tempPrefix, vv, vv_
  , symChars, isNonSymbol, nonSymbol
  , isNontrivialVV
  , symbolText, symbolString

  -- * Creating Symbols
  , Symbolic (..)
  , dummySymbol
  , intSymbol
  , tempSymbol
  , qualifySymbol
  , suffixSymbol

  -- * Located Values
  , Located (..)
  , LocSymbol, LocText
  , locAt, dummyLoc, dummyPos, dummyName, isDummy

  -- * Expressions
  , Expr (..)
  , Literal (..)
  , UnaryOp (..)
  , BinaryOp (..)
  , pattern ETrue
  , pattern EFalse
  , pattern EFalse
  , pattern EUop
  , pattern EBop
  , eVar, eVarAnn
  , eAnd, eOr

  -- * User Annotations
  , Ann(..)
  , emptyAnn
  , mkAnn
  , fromAnn

  -- * Variables
  , Variable(..)
  , mkVar, mkVarAnn
  , fromVarAnn, annotateVar

  -- * Type Constructors
  , FTycon(..), TCEmb
  , symbolFTycon, symbolFTyconAnn
  , fromFTyconAnn, annotateFTycon
  , intFTycon, boolFTycon, realFTycon, numFTycon, funcFTycon
  , listFTycon, tupleFTycon, propFTycon, hpropFTycon, strFTycon
  , isListTC, isTupTC

  -- * Sorts
  , Sort(..)
  , intSort, boolSort, realSort, numSort, funcSort
  , propSort, hpropSort, strSort
  , listSort, tupleSort
  , symbolSort, fTyconSort, sortFTycon
  , isFuncSort
  , fApp, fAppTC, fApps
  , sortSubst

  -- * Refinements
  , Reft (..)
  , Refa (..)
  , SortedReft (..)
  , reft, reft', refa
  , eqReft                  -- singleton: v == e
  , neReft                  -- singleton: v /= e
  , ueqReft                 -- singleton: v ~~ e
  , eqReft, neReft, ueqReft
  , trueReft, falseReft
  , trueRefa, falseRefa
  , trueSortedReft
  , meetReft
  , reftExpr, mapExprReft
  , shiftVV
  , isNonTrivial
  , isFunctionSortedReft
  , isSingletonReft

  -- * Qualifiers
  , Qualifier (..)

  -- * KVars
  , KVar (..)
  , intKvar

  -- * Cut Sets of KVars
  , Kuts (..)
  , ksEmpty, ksUnion

  -- * Solver Output
  , Result (..)
  , FixResult (..)
  , FixSolution
  , resultDoc, colorResult

  -- * Top-Level Constraint System
  , GInfo (..)
  , FInfo, SInfo
  , convertFormat

  -- * Constraints
  , BindId, BindMap
  , WfC (..), wfC
  , SubC, subcId, sid, senv, slhs, srhs, subC, lhsCs, rhsCs
  , SimpC (..)
  , Tag, TaggedC, WrappedC (..)

  -- * Symbol Environments
  , SEnv, SESearch (..)
  , emptySEnv, toListSEnv, fromListSEnv
  , mapSEnv, mapSEnvWithKey
  , insertSEnv, deleteSEnv, memberSEnv
  , intersectWithSEnv
  , filterSEnv
  , lookupSEnv, lookupSEnvWithDistance

  -- * Binder Environments
  , BindEnv, beBinds
  , insertBindEnv, emptyBindEnv, lookupBindEnv, mapBindEnv, adjustBindEnv
  , bindEnvFromList, bindEnvToList
  , IBindEnv
  , emptyIBindEnv, insertsIBindEnv, deleteIBindEnv, elemsIBindEnv, unionIBindEnv
  , envCs

  -- * Constraint Partition Container
  , CPart (..)

  -- * Multicore Info
  , MCInfo (..)
  , mcInfo

  -- * Propositional Class
  , Propositional(..)

  -- * Reftable Class
  , Reftable(..)

  -- * Expression Class
  , Expression(..)

  -- * Substitutions
  , Subst
  , Subable (..)
  , mkSubst, catSubst
  , emptySubst, isEmptySubst
  , keySubstSyms, targetSubstSyms
  , substExcept, subst1Except





  -- * Accessing Constraints
  , addIds, sinfo

  -- * Constructing Refinements
  , propReft                -- singleton: Prop(v) <=> p
  , predReft                -- any pred : p
  ) where

import           Debug.Trace               (trace)

import           Data.Dynamic
import           Data.Generics             (Data)
import           Data.Typeable             (Typeable)
import           GHC.Generics              (Generic)

import           Control.Arrow             (second)
import qualified Data.Foldable             as F
import           Data.Functor
import           Data.Hashable
import           Data.List                 (foldl', intersect, nub, sort, sortBy, reverse)
import           Data.Monoid               hiding ((<>))
import           Data.String
import           Data.Text                 (Text)
import qualified Data.Text                 as T
import           Data.Traversable
import           GHC.Conc                  (getNumProcessors)
import           Control.DeepSeq
import           Data.Maybe                (isJust, mapMaybe, listToMaybe, fromMaybe)
import           Text.Printf               (printf)

import           Language.Fixpoint.Config
import           Language.Fixpoint.Misc
import           Language.Fixpoint.Names
import           Text.Parsec.Pos

import           Data.Array                hiding (indices)
import qualified Data.HashMap.Strict       as M
import qualified Data.HashSet              as S

--------------------------------------------------------------------------------
-- Located Values --------------------------------------------------------------
--------------------------------------------------------------------------------

data Located a = Loc { loc  :: !SourcePos -- ^ Start Position
                     , locE :: !SourcePos -- ^ End Position
                     , val  :: a
                     } deriving (Data, Typeable, Generic)

instance (IsString a) => IsString (Located a) where
  fromString = dummyLoc . fromString

type LocSymbol = Located Symbol
type LocText   = Located Text


instance Functor Located where
  fmap f (Loc l l' x) =  Loc l l' (f x)

instance F.Foldable Located where
  foldMap f (Loc _ _ x) = f x

instance Traversable Located where
  traverse f (Loc l l' x) = Loc l l' <$> f x

instance Eq a => Eq (Located a) where
  (Loc _ _ x) == (Loc _ _ y) = x == y

instance Show a => Show (Located a) where
  show (Loc l l' x) = show x ++ " defined from: " ++ show l ++ " to: " ++ show l'

instance Ord a => Ord (Located a) where
  compare x y = compare (val x) (val y)

instance Hashable a => Hashable (Located a) where
  hashWithSalt i = hashWithSalt i . val

instance Symbolic a => Symbolic (Located a) where
  symbol = symbol . val


locAt :: String -> a -> Located a
locAt s  = Loc l l
  where
    l    = dummyPos s

dummyLoc :: a -> Located a
dummyLoc = Loc l l
  where
    l    = dummyPos "Fixpoint.Types.dummyLoc"

dummyPos   :: String -> SourcePos
dummyPos s = newPos s 0 0

isDummy :: (Symbolic a) => a -> Bool
isDummy a = symbol a == symbol dummyName

--------------------------------------------------------------------------------
-- Expressions -----------------------------------------------------------------
--------------------------------------------------------------------------------

data Expr       = Literal  !Literal
                | UnaryOp  !UnaryOp
                | BinaryOp !BinaryOp

                | Variable !Variable
                | KVar     !KVar !Subst

                | IfThenElse !Expr !Expr !Expr
                | Cast       !Expr !Sort
                | Apply      !Expr ![Expr]
                deriving (Eq, Show, Data, Typeable, Generic)

data Literal    = Bool     !Bool
                | Integer  !Integer
                | Real     !Double
                | String   !Symbol
                | Uninterp !Symbol !Sort
                deriving (Eq, Show, Data, Typeable, Generic)

data UnaryOp    = Not | Neg
                deriving (Eq, Show, Data, Typeable, Generic)

data BinaryOp   = Plus | Minus | Times | Div | Mod
                | Eq | Ne | Gt | Ge | Lt | Le | Ueq | Une
                | And | Or | Iff | Imp
                deriving (Eq, Show, Data, Typeable, Generic)


pattern ETrue :: Expr
pattern ETrue = Literal (Bool True)

pattern EFalse :: Expr
pattern EFalse = Literal (Bool False)

pattern EUop :: UnaryOp -> Expr -> Expr
pattern EUop op e = Apply (UnaryOp op) [e]

pattern EBop :: BinaryOp -> Expr -> Expr -> Expr
pattern EBop op e1 e2 = Apply (BinaryOp op) [e1, e2]


eVar :: Symbolic s => s -> Variable
eVar = Variable . mkVar

eVarAnn :: (Symbolic s, Typeable a) => s -> a -> Variable
eVarAnn s = Variable . mkVarAnn s

eAnd :: [Expr] -> Expr
eAnd [] = errorstar "eAnd: empty list"
eAnd es = foldl1' (eBop And) es

eOr :: [Expr] -> Expr
eOr [] = errorstar "eOr: empty list"
eOr es = foldl1' (eBop Or) es

--------------------------------------------------------------------------------
-- User Annotations ------------------------------------------------------------
--------------------------------------------------------------------------------

newtype Ann = Ann (Maybe Dynamic)
              deriving (Data, Typeable, Generic)

emptyAnn :: Ann
emptyAnn = Ann Nothing

mkAnn :: Typeable a => a -> Ann
mkAnn = Ann . Just . toDyn

fromAnn :: Typeable a => Ann -> Maybe a
fromAnn (Ann ann) = fromDynamic =<< ann

--------------------------------------------------------------------------------
-- Variables -------------------------------------------------------------------
--------------------------------------------------------------------------------

data Variable = V { varSym :: !Symbol
                  , varAnn :: !Ann
                  }
                deriving (Data, Typeable, Generic)


instance Eq Variable where
  (V x _) == (V y _) = x == y 

instance Ord Variable where
  compare (V x _) (V y _) = compare x y

instance Show Variable where
  show = show . varSym

instance Hashable Variable where
  hashWithSalt n = hashWithSalt n . varSym

instance IsString Variable where
  fromString = mkVar


mkVar :: Symbolic s => s -> Variable
mkVar = (`V` emptyAnn) . symbol

mkVarAnn :: (Symbolic s, Typeable a) => s -> a -> Variable
mkVarAnn sym ann = V (symbol s) (mkAnn ann)

fromVarAnn :: Typeable a => Variable -> Maybe a
fromVarAnn = fromAnn . varAnn

annotateVar :: Typeable a => Variable -> a -> Variable
annotateVar (V sym _) = V sym . mkAnn

--------------------------------------------------------------------------------
-- Type Constructors -----------------------------------------------------------
--------------------------------------------------------------------------------

type TCEmb a = M.HashMap a FTycon

data FTycon = TC { fTyconSymbol :: !Symbol
                 , fTyconAnn    :: !Ann
                 }
              deriving (Data, Typeable, Generic)


instance Eq FTycon where
  (TC x _) == (TC y _) = x == y

instance Ord FTycon where
  compare (TC x) (TC y) = compare x y

instance Show FTycon where
  show = show . fTyconSymbol

instance Hashable FTycon where
  hashWithSalt n = hashWithSalt n . fTyconSymbol

instance IsString FTycon where
  fromString = symbolFTycon


symbolFTycon :: Symbolic s => s -> FTycon
symbolFTycon = (`TC` emptyAnn) . symbol

symbolFTyconAnn :: (Symbolic s, Typeable a) => s -> a -> FTycon
symbolFTyconAnn sym ann = TC (symbol s) (mkAnn ann)

fromFTyconAnn :: Typeable a => FTycon -> Maybe a
fromFTyconAnn = fromAnn . fTyconAnn

annotateFTycon :: Typeable a => FTycon -> a -> FTycon
annotateFTycon (TC sym _) = TC sym . mkAnn


intFTyCon, boolFTyCon, realFTyCon, numFTycon, funcFTycon :: FTycon
intFTyCon   = "int"
boolFTyCon  = "bool"
realFTyCon  = "real"
numFTyCon   = "num"
funcFTyCon  = "function"

listFTycon, tupleFTycon, propFTycon, hpropFTycon, strFTycon :: FTycon
listFTyCon  = symbolFTycon listConName
tupleFTyCon = symbolFTycon tupConName
propFTyCon  = symbolFTycon propConName
hpropFTyCon = symbolFTycon hpropConName
strFTyCon   = symbolFTycon strConName


isListTC :: FTycon -> Bool
isListTC (TC c _) = c == listConName || c == "List"

isTupTC :: FTycon -> Bool
isTupTC = (== tupleFTycon)


--------------------------------------------------------------------------------
-- Sorts -----------------------------------------------------------------------
--------------------------------------------------------------------------------

data Sort = FInt
          | FReal
          | FNum                 -- ^ numeric kind for Num tyvars
          | FFrac                -- ^ numeric kind for Fractional tyvars
          | FObj  Symbol         -- ^ uninterpreted type
          | FVar  !Int           -- ^ fixpoint type variable
          | FFunc !Int ![Sort]   -- ^ type-var arity, in-ts ++ [out-t]
          | FTC   FTycon
          | FApp  Sort Sort      -- ^ constructed type
            deriving (Eq, Show, Data, Typeable, Generic)

{-@ FFunc :: Nat -> ListNE Sort -> Sort @-}


instance Monoid Sort where
  mempty            = FObj "any"
  mappend t1 t2
    | t1 == mempty  = t2
    | t2 == mempty  = t1
    | t1 == t2      = t1
    | otherwise     = errorstar $ "mappend-sort: conflicting sorts t1 =" ++ show t1 ++ " t2 = " ++ show t2


intSort, boolSort, realSort, numSort, funcSort :: Sort
intSort  = fTyconSort intFTyCon
boolSort = fTyconSort boolFTyCon
realSort = fTyconSort realFTyCon
numSort  = fTyconSort numFTyCon
funcSort = fTyconSort funcFTyCon

propSort, hpropSort, strSort :: Sort
propSort  = fTyconSort propFTyCon
hpropSort = fTyconSort hpropFTyCon
strSort   = fTyconSort strFTyCon

listSort :: Sort -> Sort
listSot = fAppTC listFTycon . return

-- TOOD: Is this correct?
tupleSort :: [Sort] -> Sort
tupleSort = fAppTC tupleFTycon


symbolSort :: Symbol -> Sort
symbolSort = fTyconSort . symbolFTycon

fTyconSort :: FTycon -> Sort
fTyconSort c
  | c == intFTyCon  = FInt
  | c == realFTyCon = FReal
  | c == numFTyCon  = FNum
  | otherwise       = FTC c

sortFTycon :: Sort -> Maybe FTycon
sortFTycon FInt    = Just intFTyCon
sortFTycon FReal   = Just realFTyCon
sortFTycon FNum    = Just numFTyCon
sortFTycon (FTC c) = Just c
sortFTycon _       = Nothing


isFuncSort :: Sort -> Maybe (Int, [Sort], Sort)
isFuncSort (FFunc n ts) = Just (n, its, t)
  where
    (its, t)            = safeUnsnoc "functionSort" ts
isFuncSort _            = Nothing


fApp :: Sort -> [Sort] -> Sort
fApp = foldl' FApp

fAppTC :: FTycon -> [Sort] -> Sort
fAppTC = fApp . fTyconSort

fApps :: Sort -> ListNE Sort
fApps = go []
  where
    go acc (FApp t1 t2) = go (t2 : acc) t1
    go acc t            = t : acc


sortSubst :: M.HashMap Symbol Sort -> Sort -> Sort
sortSubst θ t@(FObj x)   = fromMaybe t (M.lookup x θ)
sortSubst θ (FFunc n ts) = FFunc n (sortSubst θ <$> ts)
sortSubst θ (FApp t1 t2) = FApp (sortSubst θ t1) (sortSubst θ t2)
sortSubst _  t           = t

--------------------------------------------------------------------------------
-- Refinements -----------------------------------------------------------------
--------------------------------------------------------------------------------

data    Reft    = Reft { reftBind :: Symbol
                       , reftRefa :: Refa
                       }
                  deriving (Eq, Show, Data, Typeable, Generic)

newtype Refa    = Refa { refaExpr :: Expr }
                  deriving (Eq, Show, Data, Typeable, Generic)

data SortedReft = RR { sr_sort :: !Sort, sr_reft :: !Reft }
                  deriving (Eq, Show, Data, Typeable, Generic)


instance Monoid Reft where
  mempty  = trueReft
  mappend = meetReft

instance Monoid Refa where
  mempty          = trueRefa
  mappend ra1 ra2 = Refa $ eAnd [refaExpr ra1, refaExpr ra2]
  mconcat ras     = Refa $ eAnd $ map refaExpr ras

instance Monoid SortedReft where
  mempty        = RR mempty mempty
  mappend t1 t2 = RR (mappend (sr_sort t1) (sr_sort t2)) (mappend (sr_reft t1) (sr_reft t2))


reft :: Symbol -> Expr -> Reft
reft v = Reft v . Refa

reft' :: Expr -> Reft
reft' = Reft vv_ . Refa

refa :: [Expr] -> Refa
refa = Refa . eAnd

eqReft, neReft, ueqReft :: Expression a => a -> Reft
eqReft  = reft' . BinaryOp Eq  (eVar vv_)
neReft  = reft' . BinaryOp Ne  (eVar vv_)
ueqReft = reft' . BinaryOp Ueq (eVar vv_)


trueReft, falseReft :: Reft
trueReft  = reft' ETrue
falseReft = reft' EFalse

trueRefa, falseRefa :: Refa
trueRefa  = Refa ETrue
falseRefa = Refa EFalse

trueSortedReft :: Sort -> SortedReft
trueSortedReft = (`RR` trueReft)


meetReft :: Reft -> Reft -> Reft
meetReft (Reft v ra) (Reft v' ra')
  | v == v'          = Reft v  $ ra  `mappend` ra'
  | v == dummySymbol = Reft v' $ ra' `mappend` (ra  `subst1` (v , Variable $ mkVar v'))
  | otherwise        = Reft v  $ ra  `mappend` (ra' `subst1` (v', Variable $ mkVar v ))


reftExpr :: Reft -> Expr
reftExpr = refaExpr . reftRefa

mapExprReft :: (Expr -> Expr) -> Reft -> Reft
mapExprReft f (Reft v (Refa e)) = Reft v (Refa (f e))


shiftVV :: Reft -> Symbol -> Reft
shiftVV r@(Reft v r) v'
  | v == v'   = r
  | otherwise = Reft v' $ subst1 r (v, eVar v')


isNonTrivial :: Reftable r => r -> Bool
isNonTrivial = not . isTauto

isFunctionSortedReft :: SortedReft -> Bool
isFunctionSortedReft = isJust . functionSort . sr_sort


isSingletonReft :: Reft -> Maybe Expr
isSingletonReft (Reft v ra) = firstMaybe (isSingletonExpr v . refaExpr) (conjuncts ra)

isSingletonExpr :: Symbol -> Expr -> Maybe Expr
isSingletonExpr v (EBop op e1 e2)
  | e1 == EVar v && op `elem` [Eq, Ueq] = Just e2
  | e2 == EVar v && op `elem` [Eq, Ueq] = Just e1
isSingletonExpr _ _ = Nothing

--------------------------------------------------------------------------------
-- Qualifiers ------------------------------------------------------------------
--------------------------------------------------------------------------------

data Qualifier = Q { q_name   :: !Symbol           -- ^ Name
                   , q_params :: ![(Symbol, Sort)] -- ^ Parameters
                   , q_body   :: !Expr             -- ^ Body
                   , q_pos    :: !SourcePos        -- ^ Source Location
                   }
               deriving (Eq, Show, Data, Typeable, Generic)

--------------------------------------------------------------------------------
-- KVars -----------------------------------------------------------------------
--------------------------------------------------------------------------------

newtype KVar = KV { kv :: Symbol }
               deriving (Eq, Ord, Hashable, Data, Typeable, Generic, IsString)

instance Show KVar where
  show (KV x) = "$" ++ show x

intKvar :: Integer -> KVar
intKvar = KV . intSymbol "k_"

--------------------------------------------------------------------------------
-- Cut Sets of KVars -----------------------------------------------------------
--------------------------------------------------------------------------------

newtype Kuts = KS { ksVars :: S.HashSet KVar }
               deriving (Eq, Show, Data, Typeable, Generic)

instance Monoid Kuts where
  mempty        = KS S.empty
  mappend k1 k2 = KS $ S.union (ksVars k1) (ksVars k2)

ksEmpty :: Kuts
ksEmpty = KS S.empty

ksUnion :: [KVar] -> Kuts -> Kuts
ksUnion kvs (KS s') = KS (S.union (S.fromList kvs) s')

--------------------------------------------------------------------------------
-- Solver Output ---------------------------------------------------------------
--------------------------------------------------------------------------------

data Result a = Result { resStatus   :: FixResult (WrappedC a)
                       , resSolution :: M.HashMap KVar Pred
                       }
                deriving (Show, Data, Typeable, Generic)

data FixResult a = Crash [a] String
                 | Safe
                 | Unsafe ![a]
                 | UnknownError !String
                   deriving (Show, Data, Typeable, Generic)

type FixSolution = M.HashMap KVar Pred


instance Eq a => Eq (FixResult a) where
  Crash xs _ == Crash ys _        = xs == ys
  Unsafe xs == Unsafe ys          = xs == ys
  Safe      == Safe               = True
  _         == _                  = False

instance Functor FixResult where
  fmap f (Crash xs msg)   = Crash (f <$> xs) msg
  fmap f (Unsafe xs)      = Unsafe (f <$> xs)
  fmap _ Safe             = Safe
  fmap _ (UnknownError d) = UnknownError d

instance Monoid (Result a) where
  mempty        = Result mempty mempty
  mappend r1 r2 = Result stat soln
    where
      stat      = mappend (resStatus r1)   (resStatus r2)
      soln      = mappend (resSolution r1) (resSolution r2)

instance Monoid (FixResult a) where
  mempty                          = Safe
  mappend Safe x                  = x
  mappend x Safe                  = x
  mappend _ c@(Crash _ _)         = c
  mappend c@(Crash _ _) _         = c
  mappend (Unsafe xs) (Unsafe ys) = Unsafe (xs ++ ys)
  mappend u@(UnknownError _) _    = u
  mappend _ u@(UnknownError _)    = u


-- TODO: Strip out "Fixpoint"
resultDoc :: (Ord a, Fixpoint a) => FixResult a -> Doc
resultDoc Safe             = text "Safe"
resultDoc (UnknownError d) = text $ "Unknown Error: " ++ d
resultDoc (Crash xs msg)   = vcat $ text ("Crash!: " ++ msg) : (((text "CRASH:" <+>) . toFix) <$> xs)
resultDoc (Unsafe xs)      = vcat $ text "Unsafe:"           : (((text "WARNING:" <+>) . toFix) <$> xs)

colorResult :: FixResult a -> Moods
colorResult (Safe)      = Happy
colorResult (Unsafe _)  = Angry
colorResult (_)         = Sad

--------------------------------------------------------------------------------
-- Top-Level Constraint System -------------------------------------------------
--------------------------------------------------------------------------------

type FInfo a = GInfo SubC a
type SInfo a = GInfo SimpC a

data GInfo c a =
  FI { cm       :: M.HashMap Integer (c a)
     , ws       :: ![WfC a]
     , bs       :: !BindEnv
     , lits     :: !(SEnv Sort)
     , kuts     :: Kuts
     , quals    :: ![Qualifier]
     , bindInfo :: M.HashMap BindId a
     , fileName :: FilePath
     }
  deriving (Eq, Show, Functor, Data, Typeable, Generic)

instance Monoid (GInfo c a) where
  mempty        = FI M.empty mempty mempty mempty mempty mempty mempty mempty
  mappend i1 i2 = FI { cm       = mappend (cm i1)       (cm i2)
                     , ws       = mappend (ws i1)       (ws i2)
                     , bs       = mappend (bs i1)       (bs i2)
                     , lits     = mappend (lits i1)     (lits i2)
                     , kuts     = mappend (kuts i1)     (kuts i2)
                     , quals    = mappend (quals i1)    (quals i2)
                     , bindInfo = mappend (bindInfo i1) (bindInfo i2)
                     , fileName = fileName i1
                     }


convertFormat :: (Fixpoint a) => FInfo a -> SInfo a
convertFormat fi = fi' { cm = M.map subcToSimpc $ cm fi' }
  where
    fi' = foldl blowOutVV fi (M.keys $ cm fi)

subcToSimpc :: SubC a -> SimpC a
subcToSimpc s = SimpC
  { _cenv  = senv s
  , crhs   = reftExpr $ sr_reft $ srhs s
  , _cid   = sid s
  , _ctag  = stag s
  , _cinfo = sinfo s
  }

blowOutVV :: FInfo a -> Integer -> FInfo a
blowOutVV fi subcId = fi { bs = be', cm = cm' }
  where
    subc = cm fi M.! subcId
    sr   = slhs subc
    x    = reftBind $ sr_reft sr
    (bindId, be') = insertBindEnv x sr $ bs fi
    subc' = subc { _senv = insertsIBindEnv [bindId] $ senv subc }
    cm' = M.insert subcId subc' $ cm fi

--------------------------------------------------------------------------------
-- Constraints -----------------------------------------------------------------
--------------------------------------------------------------------------------

type BindId        = Int
type BindMap a     = M.HashMap BindId a -- (Symbol, SortedReft)

{-@ type Tag = { v : [Int] | len(v) = 1 } @-}
type Tag           = [Int]

data WfC a  = WfC  { wenv  :: !IBindEnv
                   , wrft  :: !SortedReft
                   , wid   :: !(Maybe Integer)
                   , winfo :: !a
                   }
              deriving (Eq, Generic, Functor)

data SubC a = SubC { _senv  :: !IBindEnv
                   ,  slhs  :: !SortedReft
                   ,  srhs  :: !SortedReft
                   , _sid   :: !(Maybe Integer)
                   , _stag  :: !Tag
                   , _sinfo :: !a
                   }
              deriving (Eq, Generic, Functor)

data SimpC a = SimpC { _cenv  :: !IBindEnv
                     ,  crhs  :: !Expr
                     , _cid   :: !(Maybe Integer)
                     , _ctag  :: !Tag
                     , _cinfo :: !a
                     }
               deriving (Generic, Functor)


wfC  :: IBindEnv -> SortedReft -> Maybe Integer -> a -> WfC a
wfC  = WfC

subC :: IBindEnv -> SortedReft -> SortedReft -> Maybe Integer -> Tag -> a -> [SubC a]
subC γ sr1 sr2 i y z = [SubC γ sr1' (sr2' r2') i y z | r2' <- conjuncts r2]
   where
     RR t1 r1          = sr1
     RR t2 r2          = sr2
     sr1'              = RR t1 $ shiftVV r1  vv'
     sr2' r2'          = RR t2 $ shiftVV r2' vv'
     vv' | Just n <- i = vv $ Just n
         | otherwise   = vvCon


subcId :: SubC a -> Integer
subcId = mfromJust "subCId" . sid

lhsCs, rhsCs :: SubC a -> Reft
lhsCs      = sr_reft . slhs
rhsCs      = sr_reft . srhs


class TaggedC c a where
  senv  :: (c a) -> IBindEnv
  sid   :: (c a) -> (Maybe Integer)
  stag  :: (c a) -> Tag
  sinfo :: (c a) -> a

instance TaggedC SimpC a where
  senv  = _cenv
  sid   = _cid
  stag  = _ctag
  sinfo = _cinfo

instance TaggedC SubC a where
  senv  = _senv
  sid   = _sid
  stag  = _stag
  sinfo = _sinfo


data WrappedC a where
  WrapC :: (TaggedC c a, Show (c a)) => {_x :: (c a)} -> WrappedC a

instance Show (WrappedC a) where
  show (WrapC x) = show x

instance TaggedC WrappedC a where
  senv (WrapC x)  = senv x
  sid (WrapC x)   = sid x
  stag (WrapC x)  = stag x
  sinfo (WrapC x) = sinfo x

--------------------------------------------------------------------------------
-- Symbol Environments ---------------------------------------------------------
--------------------------------------------------------------------------------

newtype SEnv a = SE { seBinds :: M.HashMap Symbol a }
                 deriving (Eq, Show, Monoid, Data, Typeable, Generic, Functor, F.Foldable, Traversable)

data SESearch a = Found a | Alts [Symbol]
                  deriving (Eq, Show, Data, Typeable, Generic, Functor, F.Foldable, Traversable)


emptySEnv :: SEnv a
emptySEnv = SE M.empty

toListSEnv :: SEnv a -> [(Symbol, a)]
toListSEnv (SE env)     = M.toList env

fromListSEnv ::  [(Symbol, a)] -> SEnv a
fromListSEnv = SE . M.fromList

mapSEnv :: (a1 -> a2) -> SEnv a1 -> SEnv a2
mapSEnv f (SE env) = SE $ M.map f env

mapSEnvWithKey :: (Symbol -> a1 -> a2) -> SEnv a1 -> SEnv a2
mapSEnvWithKey f (SE env) = SE $ M.mapWithKey f env

insertSEnv :: Symbol -> a -> SEnv a -> SEnv a
insertSEnv x y (SE env) = SE (M.insert x y env)

deleteSEnv :: Symbol -> SEnv a -> SEnv a
deleteSEnv x (SE env) = SE (M.delete x env)

memberSEnv :: Symbol -> SEnv a -> Bool
memberSEnv x (SE env) = M.member x env

intersectWithSEnv :: (a1 -> a2 -> a3) -> SEnv a1 -> SEnv a2 -> SEnv a3
intersectWithSEnv f (SE m1) (SE m2) = SE (M.intersectionWith f m1 m2)

filterSEnv :: (a -> Bool) -> SEnv a -> SEnv a
filterSEnv f (SE m) = SE (M.filter f m)

lookupSEnv :: Symbol -> SEnv a -> Maybe a
lookupSEnv x (SE env) = M.lookup x env


lookupSEnvWithDistance :: Symbol -> SEnv a -> SESearch a
lookupSEnvWithDistance x (SE env)
  = case M.lookup x env of
     Just z  -> Found z
     Nothing -> Alts $ symbol . T.pack <$> alts
  where
    alts       = takeMin $ zip (editDistance x' <$> ss) ss
    ss         = T.unpack . symbolText <$> fst <$> M.toList env
    x'         = T.unpack $ symbolText x
    takeMin xs = [z | (d, z) <- xs, d == getMin xs]
    getMin     = minimum . (fst <$>)

editDistance :: Eq a => [a] -> [a] -> Int
editDistance xs ys = table ! (m,n)
    where
    (m,n) = (length xs, length ys)
    x     = array (1,m) (zip [1..] xs)
    y     = array (1,n) (zip [1..] ys)

    table :: Array (Int,Int) Int
    table = array bnds [(ij, dist ij) | ij <- range bnds]
    bnds  = ((0,0),(m,n))

    dist (0,j) = j
    dist (i,0) = i
    dist (i,j) = minimum [table ! (i-1,j) + 1, table ! (i,j-1) + 1,
        if x ! i == y ! j then table ! (i-1,j-1) else 1 + table ! (i-1,j-1)]

--------------------------------------------------------------------------------
-- Global Binder Environments --------------------------------------------------
--------------------------------------------------------------------------------

data BindEnv = BE { beSize  :: Int
                  , beBinds :: BindMap (Symbol, SortedReft)
                  } deriving (Eq, Show, Functor, Data, Typeable, Generic, F.Foldable, Traversable)
-- Invariant: All BindIds in the map are less than beSize

newtype IBindEnv = FB (S.HashSet BindId)
                   deriving (Eq, Show, Data, Typeable, Generic)


instance Monoid BindEnv where
  mempty = BE 0 M.empty
  mappend (BE 0 _) b = b
  mappend b (BE 0 _) = b
  mappend _ _        = errorstar "mappend on non-trivial BindEnvs"


insertBindEnv :: Symbol -> SortedReft -> BindEnv -> (BindId, BindEnv)
insertBindEnv x r (BE n m) = (n, BE (n + 1) (M.insert n (x, r) m))

emptyBindEnv :: BindEnv
emptyBindEnv = BE 0 M.empty

lookupBindEnv :: BindId -> BindEnv -> (Symbol, SortedReft)
lookupBindEnv k (BE _ m) = fromMaybe err (M.lookup k m)
  where
    err = errorstar $ "lookupBindEnv: cannot find binder" ++ show k

mapBindEnv :: ((Symbol, SortedReft) -> (Symbol, SortedReft)) -> BindEnv -> BindEnv
mapBindEnv f (BE n m) = BE n $ M.map f m

adjustBindEnv :: ((Symbol, SortedReft) -> (Symbol, SortedReft)) -> BindId -> BindEnv -> BindEnv
adjustBindEnv f id (BE n m) = BE n $ M.adjust f id m

bindEnvFromList :: [(BindId, Symbol, SortedReft)] -> BindEnv
bindEnvFromList [] = emptyBindEnv
bindEnvFromList bs = BE (1 + maxId) be
  where
    maxId          = maximum $ fst3 <$> bs
    be             = M.fromList [(n, (x, r)) | (n, x, r) <- bs]

bindEnvToList :: BindEnv -> [(BindId, Symbol, SortedReft)]
bindEnvToList (BE _ be) = [(n, x, r) | (n, (x, r)) <- M.toList be]


emptyIBindEnv :: IBindEnv
emptyIBindEnv = FB S.empty

insertsIBindEnv :: [BindId] -> IBindEnv -> IBindEnv
insertsIBindEnv is (FB s) = FB (foldr S.insert s is)

deleteIBindEnv :: BindId -> IBindEnv -> IBindEnv
deleteIBindEnv i (FB s) = FB (S.delete i s)

elemsIBindEnv :: IBindEnv -> [BindId]
elemsIBindEnv (FB s) = S.toList s

unionIBindEnv :: IBindEnv -> IBindEnv -> IBindEnv
unionIBindEnv (FB m1) (FB m2) = FB $ m1 `S.union` m2


envCs :: BindEnv -> IBindEnv -> [(Symbol, SortedReft)]
envCs be env = [lookupBindEnv i be | i <- elemsIBindEnv env]

--------------------------------------------------------------------------------
-- Constraint Partition Container ----------------------------------------------
--------------------------------------------------------------------------------

data CPart a = CPart { pws :: [WfC a]
                     , pcm :: M.HashMap Integer (SubC a)
                     , cFileName :: FilePath
                     }

instance Monoid (CPart a) where
   mempty = CPart mempty mempty mempty
   mappend l r = CPart { pws = pws l `mappend` pws r
                       , pcm = pcm l `mappend` pcm r
                       , cFileName = cFileName l
                       }

--------------------------------------------------------------------------------
-- Multicore Info --------------------------------------------------------------
--------------------------------------------------------------------------------

data MCInfo = MCInfo { mcCores :: Int
                     , mcMinPartSize :: Int
                     , mcMaxPartSize :: Int
                     } deriving (Show)

mcInfo :: Config -> IO MCInfo
mcInfo c = do
   np <- getNumProcessors
   let nc = fromMaybe np (cores c)
   return MCInfo { mcCores = nc
                 , mcMinPartSize = minPartSize c
                 , mcMaxPartSize = maxPartSize c
                 }

--------------------------------------------------------------------------------
-- Propositional Class ---------------------------------------------------------
--------------------------------------------------------------------------------

-- TODO: Better name?
class Propositional a where
  top          :: a -> a
  bot          :: a -> a

  isTrue       :: a -> Bool
  isFalse      :: a -> Bool

  isTauto      :: a -> Bool
  isContra     :: a -> Bool

  isContingent :: a -> Bool
  isContingent x = not (isTauto x || isContra x)

  conjuncts :: a -> [a]
  meet      :: a -> a

instance Propositional () where
  top        = id
  bot        = id

  isTrue   _ = True
  isFalse  _ = False

  isTauto  _ = True
  isContra _ = False

  conjuncts  = []
  meet _ _   = ()

instance Propositional Expr where
  top _ = ETrue
  bot _ = EFalse

  isTrue  = (== ETrue)
  isFalse = (== EFalse)

  isTauto ETrue = True
  isTauto (EBop Le  x y) = x == y
  isTauto (EBop Ge  x y) = x == y
  isTauto (EBop Eq  x y) = x == y
  isTauto (EBop Ueq x y) = x == y
  isTauto (EBop Ne  (Literal x) (Literal y)) = x /= y
  isTauto (EBop Une (Literal x) (Literal y)) = x /= y
  isTauto _ = False

  isContra EFalse = False
  isContra (EBop Eq  (Literal x) (Literal y)) = x /= y
  isContra (EBop Ueq (Literal x) (Literal y)) = x /= y
  isContra (EBop Ne  x y) = x == y
  isContra (EBop Une x y) = x == y
  isContra _ = False

  conjuncts (EBop And e1 e2) = conjuncts e1 ++ conjuncts e2
  conjuncts e
    | isTauto e = []
    | otherwise = [p]

  meet = mappend

instance Propositional Reft where
  top r    = r { reftRefa = mempty }
  bot _    = falseReft

  isTrue   = isTrue  . reftRefa
  isFalse  = isFalse . reftRefa

  isTauto  = isTauto  . reftRefa
  isContra = isContra . reftRefa

  conjucts (Reft v r) = map (Reft v) (conjuncts r)
  meet                = mappend

instance Propositional Refa where
  top _ = mempty
  bot s = s { sr_reft = falseReft }

  isTrue  = isTrue  . refaExpr
  isFalse = isFalse . refaExpr

  isTauto  = all isTauto  . conjuncts . refaExpr
  isContra = any isContra . conjuncts . refaExpr

  conjuncts = map Refa . conjuncts . refaExpr
  meet      = mappend

instance Propositional SortedReft where
  top _    = mempty
  bot s    = s { sr_reft = falseReft }

  isTrue   = isTrue   . toReft
  isFalse  = isFalse  . toReft

  isTauto  = isTauto  . toReft
  isContra = isContra . toReft

  conjuncts (RR so r) = map (RR so) (conjuncts r)
  meet                = mappend

--------------------------------------------------------------------------------
-- Reftable Class --------------------------------------------------------------
--------------------------------------------------------------------------------

class (Monoid r, Propositional r, Subable r) => Reftable r where
  toReft  :: r -> Reft
  ofReft  :: Reft -> r

  params  :: r -> [Symbol]          -- ^ parameters for Reft, vv + others

instance Reftable () where
  toReft _ = mempty
  ofReft _ = mempty
  params _ = []

instance Reftable Reft where
  top r = r { reftRefa = mempty }
  bot _ = falseReft

  toReft = id
  ofReft = id

  params _ = []

instance Reftable SortedReft where
  toReft   = sr_reft
  ofReft   = error "No instance of ofReft for SortedReft"
  params _ = []

--------------------------------------------------------------------------------
-- Expression Class ------------------------------------------------------------
--------------------------------------------------------------------------------

class Expression a where
  expr :: a -> Expr

instance Expression Expr where
  expr = id

instance Expression a => Expression (Located a) where
  expr = eVar

instance Expression Symbol where
  expr = Variable . mkVar

instance Expression Bool where
  expr = Literal . Bool

instance Expression Integer where
  expr = Literal . Integer

instance Expression Int where
  expr = expr . toInteger

instance Expression Double where
  expr = Literal . Real

--------------------------------------------------------------------------------
-- Substitutions ---------------------------------------------------------------
--------------------------------------------------------------------------------

newtype Subst = Su (M.HashMap Symbol Expr)
                deriving (Eq, Show, Data, Typeable, Generic)


instance Monoid Subst where
  mempty  = emptySubst
  mappend = catSubst


-- TODO: Handle duplicate keys?
mkSubst :: [(Symbol, Expr)] -> Subst
mkSubst = Su . M.fromList . reverse

catSubst :: Subst -> Subst -> Subst
catSubst (Su x) su@(Su y) = Su (M.union (subst su x) y)


emptySubst :: Subst
emptySubst = Su M.empty

isEmptySubst :: Subst -> Bool
isEmptySubst (Su m) = M.null m


keySubstSyms :: Subst -> [Symbol]
keySubstSyms (Su m) = M.keys m

targetSubstSyms :: Subst -> [Symbol]
targetSubstSyms (Su m) = syms $ M.elems m


substExcept :: Subst -> [Symbol] -> Subst
substExcept (Su m) xs = Su $ M.filterWithKey (const . not . (`elem` xs)) xes

subst1Except :: Subable a => [Symbol] -> a -> (Symbol, Expr) -> a
subst1Except xs z su@(x, _)
  | x `elem` xs = z
  | otherwise   = subst1 z su


class Subable a where
  syms   :: a -> [Symbol]
  subst  :: Subst -> a -> a

  subst1 :: a -> (Symbol, Expr) -> a
  subst1 y (x, e) = subst1 (mkSubst [(x, e)]) y

instance Subable () where
  syms   _   = []
  subst  _ _ = ()
  subst1 _ _ = ()

instance Subable a => Subable [a] where
  syms  = concatMap syms
  subst = map . subst

instance (Subable a, Subable b) => Subable (a,b) where
  syms     (x, y) = syms x ++ syms y
  subst su (x, y) = (subst su x, subst su y)

instance Subable a => Subable (M.HashMap k a) where
  syms  = syms . M.elems
  subst = M.map . subst

instance Subable a => Subable (Located a) where
  syms     (Loc _ _  x) = syms x
  subst su (Loc l l' x) = Loc l l' (subst su x)

instance Subable Expr where
  syms = exprSymbols

  subst (Su m) e@(Variable var) = M.lookupDefault e (varSym var) m

  subst su (IfThenElse p e1 e2) = IfThenElse (subst su p) (subst su e1) (subst su e2)
  subst su (Cast e so)          = Cast (subst su e) so
  subst su (KVar kv su')        = KVar kv $ su' `catSubst` su
  subst su (Apply f xs)         = Apply (subst su f) (subst su <$> xs)
  subst _  e                    = e

exprSymbols :: Expr -> [Symbol]
exprSymbols = go
  where
    go (Variable var)       = [varSym var]
    go (KVar _ su)          = {- CUTSOLVER k : -} keySubstSyms su ++ targetSubstSyms su
    go (IfThenElse p e1 e2) = go p ++ go e1 ++ go e2
    go (Cast e _)           = go e
    go (Apply f xs)         = go f ++ concatMap go xs
    go _                    = []

instance Subable Refa where
  syms     (Refa p) = syms p
  subst su (Refa p) = Refa $ subst su p

instance Subable Reft where
  syms     (Reft v r) = v : syms r
  subst su (Reft v r) = Reft v $ subst (substExcept su [v]) r

instance Subable SortedReft where
  syms               = syms . sr_reft
  subst su (RR so r) = RR so $ subst su r

--------------------------------------------------------------------------------
-- NFData Instances ------------------------------------------------------------
--------------------------------------------------------------------------------

instance NFData SourcePos where
  rnf p = rnf f `seq` rnf l `seq` rnf c
    where
      f = sourceName   p
      l = sourceLine   p
      c = sourceColumn p

instance NFData KVar
instance NFData Kuts
instance NFData Qualifier
instance NFData FTycon
instance NFData Sort
instance NFData Sub
instance NFData Subst
instance NFData IBindEnv
instance NFData BindEnv
instance NFData Expr
instance NFData Literal
instance NFData UnaryOp
instance NFData BinaryOp
instance NFData Ann
instance NFData Variable
instance NFData Refa
instance NFData Reft
instance NFData SortedReft
instance (NFData a) => NFData (SEnv a)
instance (NFData a) => NFData (FixResult a)
instance (NFData a) => NFData (SubC a)
instance (NFData a) => NFData (WfC a)
instance (NFData a) => NFData (SimpC a)
instance (NFData (c a), NFData a) => NFData (GInfo c a)
instance (NFData a) => NFData (Located a)



















mkProp        = PBexp . EApp (dummyLoc propConName) . (: [])

------------------------------------------------------------------------
-- | Generalizing Symbol, Expression, Predicate into Classes -----------
------------------------------------------------------------------------

eProp ::  Symbolic a => a -> Pred
eProp = mkProp . eVar

propReft      ::  (Predicate a) => a -> Reft
propReft p    = Reft vv_ $ Refa $ PIff (eProp vv_) (prop p)

predReft      :: (Predicate a) => a -> Reft
predReft p    = Reft vv_ $ Refa $ prop p

---------------------------------------------------------------------------
-------- Constraint Constructor Wrappers ----------------------------------
---------------------------------------------------------------------------

--removeLhsKvars cs vs
--  = error "TODO:cutsolver: removeLhsKvars (why is this function needed?)"

-- CUTSOLVER   = cs {slhs = goRR (slhs cs)}
-- CUTSOLVER  where goRR rr                     = rr{sr_reft = goReft (sr_reft rr)}
-- CUTSOLVER        goReft (Reft(v, rs))        = Reft(v, filter f rs)
-- CUTSOLVER        f (RKvar v _) | v `elem` vs = False
-- CUTSOLVER        f r                         = True

--trueSubCKvar k = subC emptyIBindEnv mempty rhs  Nothing [0]
--  where
--    rhs        = RR mempty (Reft (vv_, Refa $ PKVar k mempty))


addIds = zipWith (\i c -> (i, shiftId i $ c {_sid = Just i})) [1..]
  where -- Adding shiftId to have distinct VV for SMT conversion
    shiftId i c = c { slhs = shiftSR i $ slhs c }
                    { srhs = shiftSR i $ srhs c }
    shiftSR i sr = sr { sr_reft = shiftR i $ sr_reft sr }
    shiftR i r@(Reft v _) = shiftVV r (v `mappend` symbol (show i))
