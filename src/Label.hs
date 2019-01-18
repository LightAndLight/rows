module Label where

import Data.Text (Text)

newtype Label = Label Text
  deriving (Eq, Show, Ord)
