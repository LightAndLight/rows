{-# language FlexibleContexts #-}
{-# language OverloadedLists #-}
{-# language OverloadedStrings #-}
{-# language TypeFamilies #-}
module Parser where

import Control.Applicative ((<**>), (<|>), many, optional)
import Data.Bifunctor (bimap)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Text (Text)

import qualified Data.List.NonEmpty as NonEmpty

import qualified Data.Text as Text

import Text.Megaparsec (MonadParsec, between, failure, try)
import Text.Megaparsec.Char
  (lowerChar, upperChar, space1, space, string, alphaNumChar, char)
import Text.Megaparsec.Char.Lexer (lexeme, symbol)

import qualified Text.Megaparsec as Parse

import Label
import Syntax
import Ty

{-# inline chainl1Try #-}
chainl1Try :: MonadParsec e s m => m a -> m (a -> a -> a) -> m a
chainl1Try p op = scan
  where
    scan = p <**> rst
    rst = try ((\f y g x -> g (f x y)) <$> op <*> p) <*> rst <|> pure id

ident :: MonadParsec e Text m => m Text
ident = fmap Text.pack $ (:) <$> lowerChar <*> many (alphaNumChar <|> char '\'')

label :: MonadParsec e Text m => m Label
label = Label <$> ident

parseTm :: MonadParsec e Text m => m (Syn Text Text)
parseTm = expr
  where
    expr =
      lexeme space $
      lambda <|>
      ann

    ann =
      (\e -> maybe e (SynAnn e)) <$>
      lexeme space restrict <*>
      optional (symbol space ":" *> parseTy)

    lambda =
      lam <$ symbol space "\\" <*>
      lexeme space ident <* symbol space "->" <*>
      expr

    restrict =
      foldl (\a b -> SynApp (SynRestrict b) a) <$>
      app <*>
      many (try (space *> symbol space "-") *> label)

    app = chainl1Try select (SynApp <$ space1)

    select =
      foldl (\a b -> SynApp (SynSelect b) a) <$>
      atom <*>
      many (try (space *> symbol space ".") *> label)

    unknown = SynUnknown <$ string "_"

    atom =
      var <|>
      record <|>
      parens <|>
      variant <|>
      unknown

    keywords :: [Text]
    keywords = ["is"]

    var = do
      i <- ident
      if i `elem` keywords
        then
          failure
            (Just $ Parse.Tokens $ NonEmpty.fromList $ Text.unpack i)
            [Parse.Label ('v' :| "ariable")]
        else pure $ SynVar i

    extendSeq =
      Left <$ symbol space "|" <*> expr <* string "}"

      <|>

      (\l e -> bimap (synExtend l e) ((l, e) :)) <$ symbol space "," <*>
      lexeme space label <* symbol space "=" <*>
      expr <*>
      extendSeq

      <|>

      Right [] <$ string "}"

    record =
      symbol space "*{" *>
      ((\l e -> either (synExtend l e) (SynRecord . (:) (l, e))) <$>
       lexeme space label <* symbol space "=" <*>
       expr <*>
       extendSeq

       <|>

       SynRecord [] <$ string "}")

    parens =
      between (symbol space "(") (string ")") $
      SynParens <$> expr

    embedSeq =
      synEmbed <$ symbol space "," <*>
      lexeme space label <*>
      embedSeq

      <|>

      symbol space "|" *> expr

    variant =
      between (symbol space "+{") (string "}") $

      synMatch <$>
      try (expr <* symbol space "is") <*>
      lexeme space label <* symbol space "?" <*>
      expr <* symbol space "|" <*>
      expr

      <|>

      (\lbl -> either (synInject lbl) (synEmbed lbl)) <$>
      lexeme space label <*>
      (fmap Left (symbol space "=" *> expr) <|>
       fmap Right embedSeq)

parseTy :: MonadParsec e Text m => m (Ty Text)
parseTy = ty
  where
    ty = lexeme space arrs

    arrs =
      (\a -> maybe a (tyArr a)) <$>
      app <*>
      optional (try (space *> symbol space "->") *> arrs)

    app = chainl1Try atom (TyApp <$ space1)

    var = TyVar <$> ident

    ctor =
      fmap
        (\x ->
           if x == "Record"
           then TyRecord
           else if x == "Variant"
           then TyVariant
           else TyCtor x) $
      (:) <$> upperChar <*> many alphaNumChar

    extendSeq =
      symbol space "|" *> ty <* string ")"

      <|>

      tyRowExtend <$ symbol space "," <*>
      lexeme space label <* symbol space ":" <*>
      ty <*>
      (extendSeq <|> TyRowEmpty <$ string ")")

    parens =
      symbol space "(" *>
      (tyRowExtend <$>
       lexeme space label <* symbol space ":" <*>
       ty <*>
       extendSeq

       <|>

       TyArr <$ symbol space "->" <* string ")"

       <|>

       ty <* string ")"

       <|>

       TyRowEmpty <$ string ")")

    atom =
      var <|>
      ctor <|>
      parens
