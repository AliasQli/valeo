{-# LANGUAGE MultiWayIf      #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}

module Valeo.TH (makeValidateMethod) where

import           Control.Monad                (forM)
import           Data.Char                    (toLower)
import           Data.Functor                 (($>))
import           Data.Text                    (Text)
import qualified Data.Text                    as T
import           Language.Haskell.TH
import           Language.Haskell.TH.Datatype
import           Valeo

nameBV :: Name -> Name
nameBV name = mkName (nameBase name ++ "V")

nameBC :: Name -> Name
nameBC name = mkName (nameBase name ++ "C")

nameSC :: Name -> Name
nameSC name = mkName $ lowerHead (nameBase name ++ "C")

defNameC :: Name -> Name
defNameC name = mkName $ "default" ++ nameBase name ++ "C"

lowerHead :: [Char] -> [Char]
lowerHead (x : xs) = toLower x : xs
lowerHead _        = undefined

toVarT :: TyVarBndr -> Type
toVarT (PlainTV nm)     = VarT nm
toVarT (KindedTV nm _k) = VarT nm

mkType :: Type -> [TyVarBndr] -> Type
mkType = foldl (\a b -> a `AppT` toVarT b)

makeV :: DatatypeInfo -> Dec
makeV DatatypeInfo{..} =
  if
    | [ConstructorInfo{..}] <- datatypeCons ->
      NewtypeD
        []
        nameV
        datatypeVars
        Nothing
        mkCon
        []
    | otherwise ->
      DataD
        []
        nameV
        datatypeVars
        Nothing
        [mkCon]
        []
  where
    nameV = nameBV datatypeName
    mkCon =
      RecC
        nameV
        (mkField <$> datatypeCons)
    mkField ConstructorInfo{..} =
      ( nameSC constructorName
      , Bang NoSourceUnpackedness NoSourceStrictness
      , mkType (ConT (nameBC constructorName)) datatypeVars
      )

makeC :: [TyVarBndr] -> ConstructorInfo -> Dec
makeC datatypeVars ConstructorInfo{..} =
  if
    | [_] <- constructorFields ->
      NewtypeD
        []
        name
        datatypeVars
        Nothing
        mkCon
        []
    | otherwise ->
      DataD
        []
        name
        datatypeVars
        Nothing
        [mkCon]
        []
  where
    mkCon =
      if
        | RecordConstructor names <- constructorVariant ->
          RecC
            name
            (mkField <$> zip names constructorFields)
        | otherwise ->
          NormalC
            name
            (mkField' <$> constructorFields)
    mkField (name, field) =
      ( nameBV name
      , Bang NoSourceUnpackedness NoSourceStrictness
      , ConT ''Validator `AppT` field
      )
    mkField' field =
      ( Bang NoSourceUnpackedness NoSourceStrictness
      , ConT ''Validator `AppT` field
      )
    name = nameBC constructorName

makeInstance :: Name -> [ConstructorInfo] -> Q Dec
makeInstance name datatypeCons = do
  let nameV = nameBV name
      t = TySynInstD $ TySynEqn Nothing (ConT ''Validated `AppT` ConT nameV) (ConT name)
  clauses <- forM (zip [0..] datatypeCons) $ \(ix, ConstructorInfo{..}) -> do
    nms <- sequence $ constructorFields $> ((,) <$> newName "v" <*> newName "x")
    let (vs, xs) = unzip nms
        cConP = ConP (nameBC constructorName) (VarP <$> vs)
        aConP = ConP constructorName (VarP <$> xs)
        vConP = ConP nameV (replicate ix WildP ++ [cConP] ++ replicate (length datatypeCons - ix - 1) WildP)
        apps = makeApp <$> zip [0..] nms
          where
            makeApp (i, (f, x)) =
              UInfixE
                (VarE 'T.pack `AppE` LitE (stringL text))
                (VarE '(-:>))
                (VarE f `AppE` VarE x)
              where
                text = case constructorVariant of
                      RecordConstructor names -> concat [nameBase constructorName, ".", nameBase (names !! i), " "]
                      _                       -> concat [nameBase constructorName, ".field", show i, " "]
        body = NormalB (foldr1 (\a b -> UInfixE a (VarE '(<>)) b) apps)
    return $
      Clause
        [vConP, aConP]
        body
        []
  let f = FunD 'makeValidator clauses
  return $ InstanceD
    Nothing
    []
    (ConT ''ValidateMethod `AppT` ConT nameV)
    [t, f]

makeDefV :: DatatypeInfo -> Dec
makeDefV DatatypeInfo{..} =
  ValD
    (VarP (mkName $ "default" ++ nameBase datatypeName ++ "V"))
    body
    []
  where
    body = NormalB $
      foldl f (ConE (nameBV datatypeName)) datatypeCons
    f e ConstructorInfo{..} = e `AppE` VarE (defNameC constructorName)

makeDefC :: ConstructorInfo -> Dec
makeDefC ConstructorInfo{..} =
  ValD
    (VarP (defNameC constructorName))
    body
    []
  where
    body = NormalB $
      foldl f (ConE (nameBC constructorName)) (constructorFields $> 'mempty)
    f e x = e `AppE` VarE x

-- No support for infix constructors.
-- TODO: Add error msg.
makeValidateMethod :: Name -> DecsQ
makeValidateMethod name = do
  info@DatatypeInfo{..} <- reifyDatatype name
  let v = makeV info
      cs = makeC datatypeVars <$> datatypeCons
      defV = makeDefV info
      defCs = makeDefC <$> datatypeCons
  i <- makeInstance name datatypeCons
  return (i : v : defV : cs ++ defCs)


-- Sample code generated:

-- data UserC
--   = UserC
--     { nameV :: Validator Text
--     , ageV  :: Validator Int
--     }

-- defaultUserC :: UserC
-- defaultUserC = UserC mempty mempty

-- data AdminC
--   = AdminC
--     { nameV       :: Validator Text
--     , permissionV :: Validator Int
--     }

-- defaultAdminC :: AdminC
-- defaultAdminC = AdminC mempty mempty

-- data UserV
--   = UserV
--     { userC  :: UserC
--     , adminC :: AdminC
--     }

-- defaultUserV :: UserV
-- defaultUserV = UserV defaultUserC defaultAdminC

-- instance ValidateInfo UserV where
--   type Validated UserV = User
--   makeValidator (UserV (UserC nameV ageV) _)         (User name age)         = "User.name " -:> nameV name <> "User.age " -:> ageV age
--   makeValidator (UserV _ (AdminC nameV permissionV)) (Admin name permission) = "Admin.name " -:> nameV name <> "Admin.permission " -:> permissionV permission
