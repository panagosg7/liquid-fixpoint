module Language.Fixpoint.Serialize (
    toFixpoint
  , writeFInfo
  ) where

import Data.Hashable

import qualified Data.HashSet as S
import qualified Data.Text    as T

import Text.Parsec.Pos
import Text.PrettyPrint.HughesPJ

import Language.Fixpoint.Misc
import Language.Fixpoint.Names
import Language.Fixpoint.Types

--------------------------------------------------------------------------------
-- Top-Level Serialization -----------------------------------------------------
--------------------------------------------------------------------------------

toFixpoint :: (Fixpoint a, Fixpoint (c a)) => Config -> GInfo c a -> Doc
toFixpoint cfg x' =    qualsDoc x'
                  $++$ kutsDoc  x'
                  $++$ conDoc   x'
                  $++$ bindsDoc x'
                  $++$ csDoc    x'
                  $++$ wsDoc    x'
                  $++$ binfoDoc x'
                  $++$ text "\n"
  where
    conDoc        = vcat     . map toFixConstant . toListSEnv . lits
    csDoc         = vcat     . map toFix . M.elems . cm
    wsDoc         = vcat     . map toFix . ws
    kutsDoc       = toFix    . kuts
    bindsDoc      = toFix    . bs
    qualsDoc      = vcat     . map toFix . quals
    metaDoc (i,d) = toFixMeta (text "bind" <+> toFix i) (toFix d)
    mdata         = metadata cfg
    binfoDoc
      | mdata     = vcat     . map metaDoc . M.toList . bindInfo
      | otherwise = \_ -> text "\n"

toFixConstant (c, so)
  = text "constant" <+> toFix c <+> text ":" <+> parens (toFix so)

writeFInfo :: (Fixpoint a, Fixpoint (c a)) => Config -> GInfo c a -> FilePath -> IO ()
writeFInfo cfg fi f = writeFile f (render $ toFixpoint cfg fi)

--------------------------------------------------------------------------------
-- Internal Traversal ----------------------------------------------------------
--------------------------------------------------------------------------------

class Fixpoint a where
  toFix :: a -> Doc


instance Fixpoint a => Fixpoint (Located a) where
  toFix = toFix . val


{-
instance (Eq a, Hashable a, Fixpoint a) => Fixpoint (S.HashSet a) where
  toFix xs = brackets $ sep $ punctuate (text ";") (toFix <$> S.toList xs)

instance Fixpoint a => Fixpoint (Maybe a) where
  toFix = maybe (text "Nothing") ((text "Just" <+>) . toFix)

instance Fixpoint a => Fixpoint [a] where
  toFix xs = brackets $ sep $ punctuate (text ";") (fmap toFix xs)

instance (Fixpoint a, Fixpoint b) => Fixpoint (a,b) where
  toFix (x,y) = toFix x <+> text ":" <+> toFix y

instance (Fixpoint a, Fixpoint b, Fixpoint c) => Fixpoint (a,b,c) where
  toFix (x,y,z) = toFix x <+> text ":" <+> toFix y <+> text ":" <+> toFix  z
-}


instance Fixpoint () where
  toFix _ = text "()"

instance Fixpoint Bool where
  toFix True  = text "True"
  toFix False = text "False"

instance Fixpoint Int where
  toFix = tshow

instance Fixpoint Integer where
  toFix = integer

instance Fixpoint Double where
  toFix = double

instance Fixpoint SourcePos where
  toFix = text . show

instance Fixpoint Symbol where
  toFix = text . encode . T.unpack . symbolText

instance Fixpoint T.Text where
  toFix = text . T.unpack


instance (Fixpoint a) => Fixpoint (SEnv a) where
   toFix (SE m) = brackets $ sep $ punctuate (text ";") $ map toFix $ hashMapToAscList m

instance Fixpoint IBindEnv where
  toFix (FB ids) = text "env" <+> brackets (sep $ punctuate (text ";") (toFix <$> S.toList ids)

instance Fixpoint BindEnv where
  toFix (BE _ m) = vcat $ map toFixBind $ hashMapToAscList m

toFixBind (i, (x, r)) = text "bind" <+> toFix i <+> toFix x <+> text ":" <+> toFix r


instance Fixpoint a => Fixpoint (SubC a) where
  toFix c     = hang (text "\n\nconstraint:") 2 bd
     where bd =   -- text "env" <+> toFix (senv c)
                  toFix (senv c)
              $+$ text "lhs" <+> toFix (slhs c)
              $+$ text "rhs" <+> toFix (srhs c)
              $+$ (toFixId (sid c) <+> text "tag" <+> toFix (stag c))
              $+$ toFixMeta (text "constraint" <+> toFixId (sid c)) (toFix (sinfo c))

instance Fixpoint a => Fixpoint (SimpC a) where
  toFix c     = hang (text "\n\nsimpleConstraint:") 2 bd
     where bd =   -- text "env" <+> toFix (senv c)
                  toFix (senv c)
              $+$ text "rhs" <+> toFix (crhs c)
              $+$ (toFixId (sid c) <+> text "tag" <+> toFix (stag c))
              $+$ toFixMeta (text "simpleConstraint" <+> toFixId (sid c)) (toFix (sinfo c))

instance Fixpoint a => Fixpoint (WfC a) where
  toFix w     = hang (text "\n\nwf:") 2 bd
    where bd  =   -- text "env"  <+> toFix (wenv w)
                  toFix (wenv w)
              $+$ text "reft" <+> toFix (wrft w)
              $+$ toFixId (wid w)
              $+$ toFixMeta (text "wf" <+> toFixId (wid w)) (toFix (winfo w))

toFixMeta :: Doc -> Doc -> Doc
toFixMeta k v = text "// META" <+> k <+> text ":" <+> v

toFixId (Just i)  = text "id" <+> tshow i
toFixId _         = text ""


instance Fixpoint Qualifier where
  toFix = toFixQual

toFixQual (Q n xts p l) =
  text "qualif" <+> text (symbolString n) <> parens args <> colon <+> toFix p <+> text "//" <+> toFix l
  where
    args = intersperse comma (toFix <$> xts)


instance Fixpoint Reft where
  toFix (Reft (_, r)) = toFix r

instance Fixpoint Refa where
  toFix (Refa p) = brackets $ sep $ punctuate (text ";") $ map toFix $ conjuncts p

instance Fixpoint SortedReft where
  toFix (RR so (Reft (v, ra))) = braces $ toFix v <+> text ":" <+> toFix so <+> text "|" <+> toFix ra


instance Fixpoint Expr where
  toFix (Literal  lit)        = toFix lit
  toFix (Operator op)         = toFix op
  toFix (Variable var)        = toFix var
  toFix (IfThenElse p e1 e2)  = parens $ text "if"   <+> toFix p
                                     <+> text "then" <+> toFix e1
                                     <+> text "else" <+> toFix e2
  toFix (Cast e so)           = parens $ toFix e <+> text ":" <+> toFix so
  toFix (ForAll xts e)        = text "forall" <+> toFix xts <+> text "." <+> toFix e
  toFix (KVar k su)           = parens $ toFix k <> toFix su

  toFix e@(Apply f xs)
    | Variable var <- f =
      toFix var <> parens (toFix xs)
    | UnaryOp op <- f, [x] <- xs =
      parens $ toFix op <+> parens (toFix x)
    | BinaryOp op <- f, [x1, x2] <- xs =
      parens $ parens (toFix x1) <+> toFix op <+> parens (toFix x2)
    | otherwise =
      errorstar $ "toFix: invalid argument: " ++ show e

instance Fixpoint Literal where
  toFix (Bool b)        = text (if b then "true" else "false")
  toFix (Integer i)     = toFix i
  toFix (Real r)        = toFix r
  toFix (String str)    = parens $ text "lit" <> toFix synSepName <> toFix str
  toFix (Uninterp u so) = parens $ text "lit" <+> text "\"" <> toFix u <> text "\"" <+> toFix so

instance Fixpoint UnaryOp where
  toFix Not             = text "~"
  toFix Neg             = text "-"

instance Fixpoint BinaryOp where
  toFix Plus            = text "+"
  toFix Minus           = text "-"
  toFix Times           = text "*"
  toFix Div             = text "/"
  toFix Mod             = text "mod"

  toFix Eq              = text "="
  toFix Ne              = text "!="
  toFix Ueq             = text "~~"
  toFix Une             = text "!~"
  toFix Gt              = text ">"
  toFix Ge              = text ">="
  toFix Lt              = text "<"
  toFix Le              = text "<="

  toFix And             = text "&&"
  toFix Or              = text "||"
  toFix Iff             = text "<=>"
  toFix Imp             = text "=>"


instance Fixpoint Sort where
  toFix (FVar i)     = text "@"   <> parens (toFix i)
  toFix FInt         = text "int"
  toFix FReal        = text "real"
  toFix FFrac        = text "frac"
  toFix (FObj x)     = toFix x
  toFix FNum         = text "num"
  toFix (FFunc n ts) = text "func" <> parens (toFix n <> text ", " <> toFix ts)
  toFix (FTC c)      = toFix c
  toFix t@(FApp _ _) = toFixFApp (fApp' t)

toFixFApp :: ListNE Sort -> Doc
toFixFApp [t]        = toFixSort t
toFixFApp [FTC c, t]
  | isListTC c       = brackets $ toFixSort t
toFixFApp ts         = parens $ intersperse space (toFixSort <$> ts)


instance Fixpoint KVar where
  toFix (KV k) = text "$" <> toFix k

instance Fixpoint Kuts where
  toFix (KS s) = vcat $ ((text "cut " <>) . toFix) <$> S.toList s


instance Fixpoint FTycon where
  toFix (TC s) = toFix s

instance Fixpoint Subst where
  toFix (Su [] ) = empty
  toFix (Su xys) = hcat $ map (\(x,y) -> brackets $ toFix x <> text ":=" <> toFix y) xys

{-
instance Fixpoint a => Show (WfC a) where
  show = showFix

instance Fixpoint a => Show (SubC a) where
  show = showFix

instance Fixpoint a => Show (SimpC a) where
  show = showFix

instance Fixpoint (SEnv a) => Show (SEnv a) where
  show = render . toFix
-}

{-
instance (Ord a, Fixpoint a) => Fixpoint (FixResult (SubC a)) where
  toFix Safe             = text "Safe"
  toFix (UnknownError d) = text $ "Unknown Error: " ++ d
  toFix (Crash xs msg)   = vcat $ [ text "Crash!" ] ++  pprSinfos "CRASH: " xs ++ [parens (text msg)]
  toFix (Unsafe xs)      = vcat $ text "Unsafe:" : pprSinfos "WARNING: " xs
-}

{-

pprSinfos :: (Ord a, Fixpoint a) => String -> [SubC a] -> [Doc]
pprSinfos msg = map ((text msg <>) . toFix) . sort . fmap sinfo

-}
