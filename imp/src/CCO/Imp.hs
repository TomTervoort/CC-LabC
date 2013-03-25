-------------------------------------------------------------------------------
-- |
-- Module      :  CCO.Imp
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

module CCO.Imp (
    -- * Syntax
    Ident        -- = String
  , Prog (..)    -- instances: Tree
  , Decl (..)    -- instances: Tree
  , Stmt (..)    -- instances: Tree
  , Exp (..)     -- instances: Tree
  , Decls        -- = [Decl]
  , Stmts        -- = [Stmt]
  , Exps         -- = [Exp]

    -- * Parser
  , parser       -- :: Component String Prog

    -- * Code generation
  , toCode       -- :: Prog -> Code
) where

import CCO.Imp.Base
import CCO.Imp.Parser  (parser)