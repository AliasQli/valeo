{-# LANGUAGE OverloadedStrings #-}

module Valeo.Common where

import           Data.Text           (Text)
import qualified Data.Text           as T
import           Data.Text.Encoding  as T (encodeUtf8)
import           Text.Email.Validate (isValid)
import           Valeo

-- | Returns 'Success' on 'True'.
-- Otherwise fail with the message.
assert :: Bool -> Text -> Validation
assert cond t = if cond
  then Success
  else Failed t

-- | The dual of 'assert'.
refute :: Bool -> Text -> Validation
refute cond t = if cond
  then Failed t
  else Success

-- | Always return 'Success'. Can be used to skip a field.
skip :: Validator a
skip = one

-- | Always fail with the given message.
block :: Text -> Validator a
block t _ = Failed t

minLen :: Int -> Validator Text
minLen i t = assert (T.length t >= i) "is too short"

maxLen :: Int -> Validator Text
maxLen i t = assert (T.length t <= i) "is too long"

min :: Integral a => a -> Validator a
min a i = assert (i >= a) "is too small"

max :: Integral a => a -> Validator a
max a i = assert (i <= a) "is too big"

email :: Validator Text
email t = assert (isValid $ T.encodeUtf8 t) "is not a valid email address"
