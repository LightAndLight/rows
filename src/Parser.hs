{-# language FlexibleContexts #-}
{-# language OverloadedStrings #-}
{-# language TypeFamilies #-}
module Parser where

import Control.Applicative ((<**>), (<|>), many, some)
import Control.Monad (void)
import Data.Text (Text)

import qualified Data.Text as Text

import Text.Megaparsec (MonadParsec, Token, between)
import Text.Megaparsec.Char (lowerChar, space, string)
import Text.Megaparsec.Char.Lexer (lexeme, symbol)

import Label
import Tm
import Ty

{-# inline chainl1 #-}
chainl1 :: MonadParsec e s m => m a -> m (a -> a -> a) -> m a
chainl1 p op = scan
  where
    scan = p <**> rst
    rst = (\f y g x -> g (f x y)) <$> op <*> p <*> rst <|> pure id

skipSpaces :: (MonadParsec e s m, Token s ~ Char) => m ()
skipSpaces = void $ many space

parseTm :: MonadParsec e Text m => m (Tm Text Text)
parseTm = expr
  where
    ident = Text.pack <$> some lowerChar

    expr =
      ann <|>
      lambda

    label = Label <$> some lowerChar

    record =
      symbol skipSpaces "*{" *>
      ((\l v -> TmApp $ TmApp (TmExtend l) v) <$>
       lexeme skipSpaces label <* symbol skipSpaces "=" <*>
       expr <* symbol skipSpaces "|" <*>
       expr <* string "}"

       <|>

       TmEmpty <$ string "}")

    atom =
      TmVar <$> ident <|>
      chainl1 (lexeme skipSpaces atom) (pure TmApp) <|>
      record <|>
      between (symbol skipSpaces "(") (string ")") expr

    lambda = lam <$> ident <*> expr

    ann =
      TmAnn <$>
      lexeme skipSpaces atom <* symbol skipSpaces ":" <*>
      parseTy

parseTy :: MonadParsec e Text m => m (Ty Text)
parseTy = _