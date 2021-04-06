{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE MultiWayIf      #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}


{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module Valeo.TH where

import           Control.Monad                (forM, unless)
import           Data.Char                    (toLower)
import           Data.Functor                 (($>))
import qualified Data.Text                    as T
import           Language.Haskell.TH
import           Language.Haskell.TH.Datatype
import           Valeo

lowerHead :: [Char] -> [Char]
lowerHead (x : xs) = toLower x : xs
lowerHead _        = undefined

mapName :: (String -> String) -> Name -> Name
mapName f = mkName . f . nameBase

nameDef :: Name -> Name
nameDef = mapName ("default" ++)

nameV :: Name -> Name
nameV = mapName (++ "V")

nameC :: Name -> Name
nameC = mapName (++ "C")

nameSC :: Name -> Name
nameSC = mapName $ lowerHead . (++ "C")

-- | Consists of 'makeSMethod', 'makeSDef', 'makeSInstQ'.
-- Applies to those types who have only __one record constructor__.
makeValeo :: Name -> DecsQ
makeValeo nm = do
  let isRecordConstructor = \case
        RecordConstructor _ -> True
        _                   -> False
  info@DatatypeInfo{..} <- reifyDatatype nm
  unless (length datatypeCons == 1) $ fail "The datatype should have exactly 1 value constructor"
  let [ConstructorInfo{..}] = datatypeCons
  unless (isRecordConstructor constructorVariant) $ fail "The value constructor should have records"
  let mth = makeSMethod info
      (sig, def) = makeSDef info
  inst <- makeSInstQ info
  return [mth, sig, def, inst]

-- | Generate the corresponding validate method datatype for the given type.
makeSMethod :: DatatypeInfo -> Dec
makeSMethod DatatypeInfo{..}
  | [ConstructorInfo{..}] <- datatypeCons
  , RecordConstructor nms <- constructorVariant =
    let fields = zip nms constructorFields
    in if length fields == 1
      then NewtypeD
        []
        nmV
        datatypeVars
        Nothing
        (conV fields)
        []
      else DataD
        []
        nmV
        datatypeVars
        Nothing
        [conV fields]
        []
  | otherwise = undefined
  where
    nmV = nameV datatypeName
    conV fields = RecC
      nmV
      (fieldV <$> fields)
    fieldV (nm, ty) =
      ( nameV nm
      , Bang NoSourceUnpackedness NoSourceStrictness
      , ConT ''Validator `AppT` ty
      )

-- | Generate the corresponding default value for the given type.
makeSDef :: DatatypeInfo -> (Dec, Dec)
makeSDef DatatypeInfo{..}
  | [ConstructorInfo{..}] <- datatypeCons =
    let nmV = nameV datatypeName
        nmDef = nameDef nmV
        body = NormalB $
          foldl AppE (ConE nmV) (constructorFields $> VarE 'mempty)
        def = ValD
          (VarP nmDef)
          body
          []
        sig = SigD nmDef (ConT nmV)
    in (sig, def)
  | otherwise = undefined

-- | Generate its 'Validatable' instance for the given type.
makeSInstQ :: DatatypeInfo -> Q Dec
makeSInstQ DatatypeInfo{..}= do
  let nmDat = datatypeName
      nmV = nameV nmDat
      tyFamDef = TySynInstD $ TySynEqn Nothing (ConT ''ValidateMethod `AppT` ConT nmDat) (ConT nmV)
      [ConstructorInfo{..}] = datatypeCons
      nmCon = constructorName
  vs <- forM constructorFields $ \_ -> newName "v"
  xs <- forM constructorFields $ \_ -> newName "x"
  let vConP = ConP nmV (VarP <$> vs)
      xConP = ConP nmCon (VarP <$> xs)
      apps = makeApp <$> zip3 [0..] vs xs
        where
          makeApp (i, f, x) =
            UInfixE
              (VarE 'T.pack `AppE` LitE (stringL text))
              (VarE '(-:>))
              (VarE f `AppE` VarE x)
            where
              RecordConstructor names = constructorVariant
              text = concat [nameBase nmCon, ".", nameBase (names !! i), " "]
      body = NormalB (foldr1 (\a b -> UInfixE a (VarE '(<.>)) b) apps)
      clause1 =
        Clause
          [vConP, xConP]
          body
          []
      validateByDef = FunD 'validateBy [clause1]
  return $
    InstanceD
      Nothing
      []
      (ConT ''Validatable `AppT` ConT nmDat)
      [tyFamDef, validateByDef]

-- defNameC :: Name -> Name
-- defNameC name = mkName $ "default" ++ nameBase name ++ "C"

-- toVarT :: TyVarBndr -> Type
-- toVarT (PlainTV nm)     = VarT nm
-- toVarT (KindedTV nm _k) = VarT nm

-- mkType :: Type -> [TyVarBndr] -> Type
-- mkType = foldl (\a b -> a `AppT` toVarT b)

-- makeV :: DatatypeInfo -> Dec
-- makeV DatatypeInfo{..} =
--   if
--     | [ConstructorInfo{..}] <- datatypeCons ->
--       NewtypeD
--         []
--         nameV
--         datatypeVars
--         Nothing
--         conV
--         []
--     | otherwise ->
--       DataD
--         []
--         nameV
--         datatypeVars
--         Nothing
--         [conV]
--         []
--   where
--     nameV = nameBV datatypeName
--     conV =
--       RecC
--         nameV
--         (fieldV <$> datatypeCons)
--     fieldV ConstructorInfo{..} =
--       ( nameSC constructorName
--       , Bang NoSourceUnpackedness NoSourceStrictness
--       , mkType (ConT (nameBC constructorName)) datatypeVars
--       )

-- makeC :: [TyVarBndr] -> ConstructorInfo -> Dec
-- makeC datatypeVars ConstructorInfo{..} =
--   if
--     | [_] <- constructorFields ->
--       NewtypeD
--         []
--         name
--         datatypeVars
--         Nothing
--         conV
--         []
--     | otherwise ->
--       DataD
--         []
--         name
--         datatypeVars
--         Nothing
--         [conV]
--         []
--   where
--     conV =
--       if
--         | RecordConstructor names <- constructorVariant ->
--           RecC
--             name
--             (fieldV <$> zip names constructorFields)
--         | otherwise ->
--           NormalC
--             name
--             (fieldV' <$> constructorFields)
--     fieldV (name, field) =
--       ( nameBV name
--       , Bang NoSourceUnpackedness NoSourceStrictness
--       , ConT ''Validator `AppT` field
--       )
--     fieldV' field =
--       ( Bang NoSourceUnpackedness NoSourceStrictness
--       , ConT ''Validator `AppT` field
--       )
--     name = nameBC constructorName

-- makeInstance :: Name -> [ConstructorInfo] -> Q Dec
-- makeInstance name datatypeCons = do
--   let nameV = nameBV name
--       t = TySynInstD $ TySynEqn Nothing (ConT ''Validated `AppT` ConT nameV) (ConT name)
--   clauses <- forM (zip [0..] datatypeCons) $ \(ix, ConstructorInfo{..}) -> do
--     nms <- sequence $ constructorFields $> ((,) <$> newName "v" <*> newName "x")
--     let (vs, xs) = unzip nms
--         cConP = ConP (nameBC constructorName) (VarP <$> vs)
--         aConP = ConP constructorName (VarP <$> xs)
--         vConP = ConP nameV (replicate ix WildP ++ [cConP] ++ replicate (length datatypeCons - ix - 1) WildP)
--         apps = makeApp <$> zip [0..] nms
--           where
--             makeApp (i, (f, x)) =
--               UInfixE
--                 (VarE 'T.pack `AppE` LitE (stringL text))
--                 (VarE '(-:>))
--                 (VarE f `AppE` VarE x)
--               where
--                 text = case constructorVariant of
--                       RecordConstructor names -> concat [nameBase constructorName, ".", nameBase (names !! i), " "]
--                       _                       -> concat [nameBase constructorName, ".field", show i, " "]
--         body = NormalB (foldr1 (\a b -> UInfixE a (VarE '(<>)) b) apps)
--     return $
--       Clause
--         [vConP, aConP]
--         body
--         []
--   let f = FunD 'makeValidator clauses
--   return $ InstanceD
--     Nothing
--     []
--     (ConT ''ValidateMethod `AppT` ConT nameV)
--     [t, f]

-- makeDefV :: DatatypeInfo -> Dec
-- makeDefV DatatypeInfo{..} =
--   ValD
--     (VarP (mkName $ "default" ++ nameBase datatypeName ++ "V"))
--     body
--     []
--   where
--     body = NormalB $
--       foldl f (ConE (nameBV datatypeName)) datatypeCons
--     f e ConstructorInfo{..} = e `AppE` VarE (defNameC constructorName)

-- makeDefC :: ConstructorInfo -> Dec
-- makeDefC ConstructorInfo{..} =
--   ValD
--     (VarP (defNameC constructorName))
--     body
--     []
--   where
--     body = NormalB $
--       foldl f (ConE (nameBC constructorName)) (constructorFields $> 'mempty)
--     f e x = e `AppE` VarE x

-- -- No support for infix constructors.
-- -- TODO: Add error msg.
-- makeValidateMethod :: Name -> DecsQ
-- makeValidateMethod name = do
--   info@DatatypeInfo{..} <- reifyDatatype name
--   let v = makeV info
--       cs = makeC datatypeVars <$> datatypeCons
--       defV = makeDefV info
--       defCs = makeDefC <$> datatypeCons
--   i <- makeInstance name datatypeCons
--   return (i : v : defV : cs ++ defCs)
