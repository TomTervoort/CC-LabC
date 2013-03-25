-------------------------------------------------------------------------------
-- |
-- Module      :  CCO.Imp.Parser
-- Copyright   :  (c) 2008 Utrecht University
-- License     :  All rights reserved
--
-- Maintainer  :  stefan@cs.uu.nl
-- Stability   :  provisional
-- Portability :  portable
--
-- A 'Parser' for a simple imperative language.
--
-------------------------------------------------------------------------------

module CCO.Imp.Parser (
    -- * Parser
    parser    -- :: Component String Prog
) where

import CCO.Imp.Base                  
import CCO.Imp.Lexer
import CCO.Component                 (Component)
import qualified CCO.Component as C  (parser)
import CCO.Parsing
import Control.Applicative

-------------------------------------------------------------------------------
-- Token parsers
-------------------------------------------------------------------------------

-- | Type of 'Parser's that consume symbols described by 'Token's.
type TokenParser = Parser Token

-------------------------------------------------------------------------------
-- Parser
-------------------------------------------------------------------------------

-- A 'Component' for parsing arithmetic and boolean expressions.
parser :: Component String Prog
parser = C.parser lexer (pProg <* eof)

-- | Parses a 'Prog'.
pProg :: TokenParser Prog
pProg = TopLevelDecls <$> pDecls

-- | Parses a 'Decl'.
pDecl :: TokenParser Decl
pDecl = VarDecl <$ keyword "var" <*> ident <* spec ';'
    <|> FunDecl <$ keyword "function" <*> ident <*
                   spec '(' <*> manySepBy (spec ',') ident <* spec ')' <*> 
                   pStmts
    <!> "declaration"

-- | Parses a 'Stmt'.
pStmt :: TokenParser Stmt
pStmt = Empty  <$  spec ';'
    <|> Decl   <$> pDecl
    <|> Assign <$> ident <* operator "=" <*> pExp <* spec ';'
    <|> Call_  <$> ident <*> pExps <* spec ';'
    <|> Print  <$  keyword "print" <*> pExp <* spec ';'
    <|> Return <$  keyword "return" <*> pExp <* spec ';'
    <|> If     <$  keyword "if" <* spec '(' <*> pExp <* spec ')' <*> pStmt <*
                   keyword "else" <*> pStmt
    <|> Block  <$> pStmts
    <!> "statement"

-- | Parses an 'Exp'.
pExp :: TokenParser Exp
pExp =  pExpEqPrio <!> "expression"
  where
    pOpEqPrio   = Lt <$ operator "<" <|> Eq <$ operator "==" <|>
                  Gt <$ operator ">" <!> "operator"
    pOpAddPrio  = Add <$ operator "+" <|> Sub <$ operator "-"  <!> "operator"
    pOpMulPrio  = Mul <$ operator "*" <|> Div <$ operator "/"  <!> "operator"
    pExpEqPrio  = pExpAddPrio <**>
                  (flip <$> pOpEqPrio <*> pExpAddPrio `opt` id)
    pExpAddPrio = chainl pOpAddPrio pExpMulPrio
    pExpMulPrio = chainl pOpMulPrio pExpBase
    pExpBase    = Int <$> ((negate <$ operator "-" `opt` id) <*> int) <|>
                  False_ <$ keyword "false" <|> True_ <$ keyword "true" <|>
                  ident <**> (flip Call <$> pExps `opt` Var) <|>
                  spec '(' *> pExp <* spec ')'

-- | Parses 'Decl's.
pDecls :: TokenParser Decls
pDecls = many pDecl

-- | Parses 'Stmt's.
pStmts :: TokenParser Stmts
pStmts = spec '{' *> many pStmt <* spec '}'

-- | Parses 'Exps'.
pExps :: TokenParser Exps
pExps = spec '(' *> manySepBy (spec ',') pExp <* spec ')'