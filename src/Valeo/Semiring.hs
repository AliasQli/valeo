module Valeo.Semiring where

import           Data.Monoid ()

(<+>) :: Monoid m => m -> m -> m
(<+>) = mappend

infixl 5 <+>

zero :: Monoid m => m
zero = mempty

class Monoid m => Semiring m where
  one :: m
  (<.>) :: m -> m -> m

infixl 6 <.>
