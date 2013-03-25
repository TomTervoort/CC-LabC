-------------------------------------------------------------------------------
-- |
-- Module      :  CCO.Imp.Lexer
-- Copyright   :  (c) 2008 Utrecht University
-- License     :  All rights reserved
--
-- Maintainer  :  stefan@cs.uu.nl
-- Stability   :  provisional
-- Portability :  portable
--
-- A 'Lexer' for a simple imperative language.
--
-------------------------------------------------------------------------------

module CCO.Imp.Lexer (
    -- * Tokens
    Token      -- abstract, instance: Symbol

    -- * Lexer
  , lexer      -- :: Lexer Token

    -- * Token parser
  , int        -- :: Parser Token Int
  , keyword    -- :: String -> Parser Token String
  , ident      -- :: Parser Token String
  , operator   -- :: String -> Parser Token String
  , spec       -- :: Char -> Parser Token Char
) where

import CCO.Imp.Base  (Ident)
import CCO.Lexing hiding (satisfy)
import CCO.Parsing   (Symbol (describe), Parser, satisfy, (<!>))
import Control.Applicative

-------------------------------------------------------------------------------
-- Tokens
-------------------------------------------------------------------------------

-- | Type of tokens.
data Token
  = Int      { fromNum      :: Int    }    -- ^ Integer constant.
  | Keyword  { fromKeyword  :: String }    -- ^ Keyword.
  | Ident    { fromIdent    :: Ident  }    -- ^ Identifier.
  | Operator { fromOperator :: String }    -- ^ Operator.
  | Spec     { fromSpec     :: Char   }    -- ^ Special character.

instance Symbol Token where
  describe (Int _)      lexeme = "integer constant " ++ lexeme
  describe (Keyword _)  lexeme = "keyword "          ++ lexeme
  describe (Ident _)    lexeme = "identifier "       ++ lexeme
  describe (Operator _) lexeme = "operator "         ++ lexeme
  describe (Spec _)     lexeme =                        lexeme

-- | Retrieves whether a 'Token' is an 'Int'.
isInt :: Token -> Bool
isInt (Int _) = True
isInt _       = False

-- | Retrieves whether a 'Token' is a 'Keyword'.
isKeyword :: Token -> Bool
isKeyword (Keyword _) = True
isKeyword _           = False

-- | Retrieves whether a 'Token' is a 'Keyword'.
isIdent :: Token -> Bool
isIdent (Ident _) = True
isIdent _         = False

-- | Retrieves whether a 'Token' is an 'Operator'.
isOperator :: Token -> Bool
isOperator (Operator _) = True
isOperator _            = False

-- | Retrieves whether a 'Token' is a 'Spec'.
isSpec :: Token -> Bool
isSpec (Spec _) = True
isSpec _        = False

-------------------------------------------------------------------------------
-- Lexer
-------------------------------------------------------------------------------

-- | A 'Lexer' that recognises (and ignores) whitespace.
layout_ :: Lexer Token
layout_ = ignore (some (anyCharFrom " \n\t"))

-- | A 'Lexer' that recognises 'Int' tokens.
int_ :: Lexer Token
int_ = (Int . foldl (\n i -> 10 * n + i) 0) <$> some digit_

-- | A 'Lexer' that recognises 'Keyword' tokens.
keyword_ :: Lexer Token
keyword_ =  fmap Keyword $
            string "else" <|> string "false" <|> string "function" <|>
            string "if" <|> string "print" <|> string "return" <|>
            string "true" <|> string "var"

-- | A 'Lexer' that recognises 'Ident' tokens.
ident_ :: Lexer Token
ident_ =  fmap Ident $
          (:) <$> (lower <|> char '_') <*> many (alphaNum <|> char '_')

-- | A 'Lexer' that recognises 'Operator' tokens.
operator_ :: Lexer Token
operator_ =  fmap Operator $
             string "*" <|> string "-" <|> string "==" <|> string "+" <|> 
             string "=" <|> string "<" <|> string ">" <|> string "/"

-- | A 'Lexer' that recognises 'Spec' tokens.
spec_ :: Lexer Token
spec_ = Spec <$> anyCharFrom "(){};,"

-- | The 'Lexer' for the simple imperative language.
lexer :: Lexer Token
lexer = layout_ <|> int_ <|> keyword_ <|> ident_ <|> operator_ <|> spec_

-------------------------------------------------------------------------------
-- Token parsers
-------------------------------------------------------------------------------

-- | A 'Parser' that recognises integer constants.
int :: Parser Token Int
int = fromNum <$> satisfy isInt <!> "integer constant"

-- | A 'Parser' that recognises a specified keyword.
keyword :: String -> Parser Token String
keyword key = fromKeyword <$>
              satisfy (\tok -> isKeyword tok && fromKeyword tok == key) <!>
              "keyword " ++ key

-- | A 'Parser' that recognises identifiers.
ident :: Parser Token Ident
ident = fromIdent <$> satisfy isIdent <!> "identifier"

-- | A 'Parser' that recognises a specified operator.
operator :: String -> Parser Token String
operator op = fromOperator <$>
              satisfy (\tok -> isOperator tok && fromOperator tok == op) <!>
              "operator " ++ op

-- | A 'Parser' that recognises a specified special character.
spec :: Char -> Parser Token Char
spec c = fromSpec <$>
         satisfy (\tok -> isSpec tok && fromSpec tok == c) <!>
         [c]