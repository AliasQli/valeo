{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE RecordWildCards        #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeSynonymInstances   #-}

module Valeo(module Valeo, module Valeo.Semiring) where

import           Data.Text      (Text)
import           Valeo.Semiring

-- | The result of a validation.
--
-- 'Validation' can be seen as a 'Semiring' except that:
--
--   * Error message produced by @a <+> b@ and @b <+> a@ is not the same (but contains the same information).
--
--   * 'zero' is actually not the right annihilator of '<.>' (@Fail s <.> zero = Fail s@).
--
-- where '<+>' acts like /or/ while '<.>' like /and/.
data Validation
  = Failed Text
  | Success
  deriving (Show, Eq, Ord)

instance Semigroup Validation where
  (Failed a) <> (Failed b) = Failed (a <> " and " <> b)
  _          <>  _         = Success

instance Monoid Validation where
  mempty = Failed "is always rejected"

instance Semiring Validation where
  one = Success
  (Failed s) <.> _ = Failed s
  Success    <.> v = v

-- | Lift an operation on failing message to
-- an operation on 'Validation'.
map :: (Text -> Text) -> Validation -> Validation
map _ Success    = Success
map f (Failed s) = Failed (f s)

-- | Inject some 'Text' to a 'Validation' failure.
(-:>) :: Text -> Validation -> Validation
s -:> v = Valeo.map (s <>) v

infixl 7 -:>

-- | 'Validator' also forms a 'Semiring'.
type Validator a = a -> Validation

instance Semiring (Validator a) where
  one = const Success
  (v1 <.> v2) a = v1 a <.> v2 a

-- | 'ValidateMethod' represents a method to validate a data type.
-- Instances of this class should be autogenerated by 'makeValidateMethod'.
class Validatable a where
  -- | The data type this method validates.
  type ValidateMethod a = r | r -> a
  -- | Make a validator from the method.
  validateBy :: ValidateMethod a -> Validator a

class Validatable a => DefaultValidate a where
  validateMethod :: ValidateMethod a

validate :: DefaultValidate a => Validator a
validate = validateBy validateMethod
