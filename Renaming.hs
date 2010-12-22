{-# LANGUAGE PatternGuards, GeneralizedNewtypeDeriving #-}
module Renaming (
    Renaming(..),
    emptyRenaming, mkRenaming, mkIdentityRenaming,
    insertRenaming, insertRenamings,
    rename, rename_maybe, safeRename, unrename,
    renameBinder, renameBinders,
    renameRenaming,
    foldRenaming
  ) where

import Name
import Utilities

import qualified Data.Map as M


type In a = a
type Out a = a


newtype Renaming = Renaming { unRenaming :: M.Map (In Name) (Out Name) }
                 deriving (Show, NFData)

instance Pretty Renaming where
    pPrintPrec level _ rn = vcat [ pPrintPrec level 0 x <+> text "|->" <+> pPrintPrec level 0 x'
                                 | (x, x') <- M.toList (unRenaming rn)]


emptyRenaming :: Renaming
emptyRenaming = Renaming M.empty

mkRenaming :: [(Name, Name)] -> Renaming
mkRenaming = Renaming . M.fromList

mkIdentityRenaming :: [Name] -> Renaming
mkIdentityRenaming = mkRenaming . map (id &&& id)

insertRenaming :: In Name -> Out Name -> Renaming -> Renaming
insertRenaming n n' = Renaming . M.insert n n' . unRenaming

insertRenamings :: [(In Name, Out Name)] -> Renaming -> Renaming
insertRenamings = flip $ foldr (uncurry insertRenaming)

rename :: Renaming -> In Name -> Out Name
rename = safeRename' Nothing

safeRename :: String -> Renaming -> In Name -> Out Name
safeRename = safeRename' . Just

safeRename' :: Maybe String -> Renaming -> In Name -> Out Name
safeRename' mb_stk rn n | Just n' <- rename_maybe rn n = n'
                        | otherwise                    = error $ show (text "Name" <+> pPrint n <+> text "out of scope" <+> maybe empty (\stk -> text "in" <+> text stk) mb_stk <> text "! Renaming:" $$ pPrint rn)

rename_maybe :: Renaming -> In Name -> Maybe (Out Name)
rename_maybe rn n = M.lookup n (unRenaming rn)

unrename :: Renaming -> Out Name -> [In Name]
unrename rn n' = [m | (m, m') <- M.toList (unRenaming rn), m' == n']

renameBinder :: IdSupply -> Renaming -> In Name -> (IdSupply, Renaming, Out Name)
renameBinder ids rn n = (ids', insertRenaming n n' rn, n')
  where (ids', n') = freshName ids (name_string n)

renameBinders :: IdSupply -> Renaming -> [In Name] -> (IdSupply, Renaming, [Out Name])
renameBinders ids rn = reassociate . mapAccumL ((associate .) . uncurry renameBinder) (ids, rn)
  where associate   (ids, rn, n)    = ((ids, rn), n)
        reassociate ((ids, rn), ns) = (ids, rn, ns)

-- NB: throws away something from the Renaming being renamed if it is not in the domain of rn_by.
-- This is useful behaviour for the term normalisation logic in the supercompiler, because the
-- "normalising" renaming will only contain entries for actual free variables, but the "internal"
-- renamings (e.g. those in the Heaps' In Terms') may contain many more entries.
renameRenaming :: Renaming -> Renaming -> Renaming
renameRenaming rn_by = Renaming . M.mapMaybe (rename_maybe rn_by) . unRenaming

foldRenaming :: (In Name -> Out Name -> b -> b) -> b -> Renaming -> b
foldRenaming f b = M.foldrWithKey f b . unRenaming

