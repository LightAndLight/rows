module Output where

class Output m where
  output :: String -> m ()
  outputWith :: (a -> m b) -> a -> m ()
