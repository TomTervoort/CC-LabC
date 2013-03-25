-------------------------------------------------------------------------------
-- |
-- Module      :  CCO.Imp.Base
-- Copyright   :  (c) 2008 Utrecht University
-- License     :  All rights reserved
--
-- Maintainer  :  stefan@cs.uu.nl
-- Stability   :  provisional
-- Portability :  portable
--
-- A simple imperative language.
--
-------------------------------------------------------------------------------

module CCO.Imp.Base (
    -- * Syntax
    Ident        -- = String
  , Prog (..)    -- instances: Tree
  , Decl (..)    -- instances: Decl
  , Stmt (..)    -- instances: Tree
  , Exp (..)     -- instances: Tree
  , Decls        -- = [Decl]
  , Stmts        -- = [Stmt]
  , Exps         -- = [Exp]

    -- * Code generation
  , toCode       -- :: Prog -> Code
) where

import CCO.Imp.AG
import CCO.Ssm              (Code)
import CCO.Tree             (ATerm (App), Tree (fromTree, toTree))
import CCO.Tree.Parser      (parseTree, app, arg)
import Control.Applicative  (Applicative (pure, (<*>)), (<$>))

-------------------------------------------------------------------------------
-- Tree instances
-------------------------------------------------------------------------------

instance Tree Prog where
  fromTree (TopLevelDecls ds) = App "TopLevelDecls" [fromTree ds]
  toTree = parseTree [app "TopLevelDecls" (TopLevelDecls <$> arg)]

instance Tree Decl where
  fromTree (VarDecl x)      = App "VarDecl" [fromTree x]
  fromTree (FunDecl f xs b) =
    App "FunDecl" [fromTree f, fromTree xs, fromTree b]  

  toTree = parseTree [ app "VarDecl" (VarDecl <$> arg                )
                     , app "FunDecl" (FunDecl <$> arg <*> arg <*> arg)
                     ]

instance Tree Stmt where
  fromTree Empty            = App "Empty"   []
  fromTree (Decl d)         = App "Decl"    [fromTree d]
  fromTree (Assign x e)     = App "Assign"  [fromTree x, fromTree e]
  fromTree (Call_ f es)     = App "Call"    [fromTree f, fromTree es]
  fromTree (Print e)        = App "Print"   [fromTree e]
  fromTree (Return e)       = App "Return"  [fromTree e]
  fromTree (If e s1 s2)     = App "If"      [fromTree e, fromTree s1,
                                             fromTree s2]
  fromTree (Block b)        = App "Block"   [fromTree b]

  toTree = parseTree [ app "Empty"  (pure Empty                     )
                     , app "Decl"   (Decl    <$> arg                )
                     , app "Assign" (Assign  <$> arg <*> arg        )
                     , app "Call"   (Call_   <$> arg <*> arg        )
                     , app "Print"  (Print   <$> arg                )
                     , app "Return" (Return  <$> arg                )
                     , app "If"     (If      <$> arg <*> arg <*> arg)
                     , app "Block"  (Block   <$> arg                )
                     ]

instance Tree Exp where
  fromTree (Int n)     = App "Int"   [fromTree n]
  fromTree False_      = App "False" []
  fromTree True_       = App "True"  []
  fromTree (Var x)     = App "Var"   [fromTree x]
  fromTree (Call f es) = App "Call"  [fromTree f, fromTree es]
  fromTree (Add e1 e2) = App "Add"   [fromTree e1, fromTree e2]
  fromTree (Sub e1 e2) = App "Sub"   [fromTree e1, fromTree e2]
  fromTree (Mul e1 e2) = App "Mul"   [fromTree e1, fromTree e2]
  fromTree (Div e1 e2) = App "Div"   [fromTree e1, fromTree e2]
  fromTree (Lt e1 e2)  = App "Lt"    [fromTree e1, fromTree e2]
  fromTree (Eq e1 e2)  = App "Eq"    [fromTree e1, fromTree e2]
  fromTree (Gt e1 e2)  = App "Gt"    [fromTree e1, fromTree e2]

  toTree = parseTree [ app "Int"   (Int  <$> arg         )
                     , app "False" (pure False_          )
                     , app "True"  (pure True_           )
                     , app "Var"   (Var  <$> arg         )
                     , app "Call"  (Call <$> arg <*> arg )
                     , app "Add"   (Add  <$> arg <*> arg )
                     , app "Sub"   (Sub  <$> arg <*> arg )
                     , app "Mul"   (Mul  <$> arg <*> arg )
                     , app "Div"   (Div  <$> arg <*> arg )
                     , app "Lt"    (Lt   <$> arg <*> arg  )
                     , app "Eq"    (Eq   <$> arg <*> arg  )
                     , app "Gt"    (Gt   <$> arg <*> arg  )
                     ]

-------------------------------------------------------------------------------
-- Code generation
-------------------------------------------------------------------------------

-- | Generates SSM code for a 'Prog'.
toCode :: Prog -> Code
toCode p = code_Syn_Prog (wrap_Prog (sem_Prog p) Inh_Prog)