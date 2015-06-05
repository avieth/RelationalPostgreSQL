{-|
Module      : 
Description : 
Copyright   : (c) Alexander Vieth, 2015
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

import qualified Data.Text as T
import Control.Monad
import Control.Monad.Free (iterM)
import Data.String
import Data.Proxy
import Data.Relational
import Data.Relational.RelationalF
import Data.Relational.Interpreter
import Data.Relational.PostgreSQL
import Database.PostgreSQL.Simple
import System.Environment

type IdColumn = '( "id", T.Text )

idColumn :: Column IdColumn
idColumn = column

type KeyColumn = '( "key", T.Text )

keyColumn :: Column KeyColumn
keyColumn = column

type ValueColumn = '( "value", T.Text )

valueColumn :: Column ValueColumn
valueColumn = column

type PropertiesSchema = '[ IdColumn, KeyColumn, ValueColumn ]

propertiesSchema :: Schema PropertiesSchema
propertiesSchema = schema Proxy

type PropertiesTable = '( "properties", PropertiesSchema )

propertiesTable :: Table PropertiesTable
propertiesTable = table propertiesSchema

type ExampleDatabase = '[ PropertiesTable ]

makeSelect :: [(T.Text, T.Text)] -> Relational ExampleDatabase [Row '[IdColumn]]
makeSelect = rfrelation . makeSelect'

makeSelect' :: [(T.Text, T.Text)] -> Relation ExampleDatabase '[IdColumn]
makeSelect' lst = case lst of
    [(key, val)] -> makeSelect1 (key, val)
    x : rest -> Intersection (makeSelect1 x) (makeSelect' rest)

makeSelect1 :: (T.Text, T.Text) -> Relation ExampleDatabase '[IdColumn]
makeSelect1 (key, value) = Selection (Select propertiesTable projection condition)
  where
    projection = idColumn :+| EndProject
    condition = keyColumn .==. key .||. false .&&. valueColumn .==. value .||. false .&&. true

makeInsert :: T.Text -> T.Text -> T.Text -> Relational ExampleDatabase ()
makeInsert id key value = rfinsert (Insert propertiesTable row)
  where
    row =   (fromColumnAndValue idColumn id)
        :&| (fromColumnAndValue keyColumn key)
        :&| (fromColumnAndValue valueColumn value)
        :&| EndRow

makeUpdate :: T.Text -> T.Text -> T.Text -> Relational ExampleDatabase ()
makeUpdate id key value = rfupdate (Update propertiesTable projection condition row)
  where
    projection = valueColumn :+| EndProject
    row = (fromColumnAndValue valueColumn value) :&| EndRow
    condition = idColumn .==. id .||. false .&&. keyColumn .==. key .||. false .&&. true

makeDelete :: T.Text -> T.Text -> Relational ExampleDatabase ()
makeDelete id key = rfdelete (Delete propertiesTable condition)
  where
    condition = idColumn .==. id .||. false .&&. keyColumn .==. key .||. false .&&. true

main = do
    args <- getArgs
    let action = head args
    let parameters = fmap fromString (tail args) :: [T.Text]
    case action of
        "select" -> mainSelect parameters
        "insert" -> mainInsert parameters
        "update" -> mainUpdate parameters
        "delete" -> mainDelete parameters

mainSelect args =
    let keysVals = makePairs args
        proxy :: Proxy (PostgresInterpreter IO)
        proxy = Proxy
        term = iterM (interpreter proxy) (makeSelect keysVals)
    in  do outcome <- runPostgresT (defaultConnectInfo { connectUser="alex" }) Prelude.id term
           print outcome
  where
    makePairs list = case list of
        [] -> []
        x : y : rest -> (x, y) : (makePairs rest)

mainInsert args =
    let id = args !! 0
        key = args !! 1
        value = args !! 2
        proxy :: Proxy (PostgresInterpreter IO)
        proxy = Proxy
        term = iterM (interpreter proxy) (makeInsert id key value)
    in  runPostgresT (defaultConnectInfo { connectUser="alex" }) Prelude.id term

mainUpdate args =
    let id = args !! 0
        key = args !! 1
        value = args !! 2
        proxy :: Proxy (PostgresInterpreter IO)
        proxy = Proxy
        term = iterM (interpreter proxy) (makeUpdate id key value)
    in  runPostgresT (defaultConnectInfo { connectUser="alex" }) Prelude.id term

mainDelete args =
    let id = args !! 0
        key = args !! 1
        proxy :: Proxy (PostgresInterpreter IO)
        proxy = Proxy
        term = iterM (interpreter proxy) (makeDelete id key)
    in  runPostgresT (defaultConnectInfo { connectUser="alex" }) Prelude.id term
