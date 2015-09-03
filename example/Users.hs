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
{-# LANGUAGE ScopedTypeVariables #-}

import GHC.TypeLits (Symbol, KnownSymbol)
import qualified Data.Text as T
import Control.Monad
import Control.Monad.Free (iterM, liftF)
import Data.TypeNat.Nat
import Data.String
import Data.Proxy
import Data.Relational
import Data.Relational.RelationalF
import Data.Relational.Interpreter
import Data.Relational.PostgreSQL
import Database.PostgreSQL.Simple
import System.Environment

type UsernameColumn = '( "username", T.Text )

usernameColumn :: Column UsernameColumn
usernameColumn = column

type EmailColumn = '( "email", T.Text )

emailColumn :: Column EmailColumn
emailColumn = column

type UsersSchema = '[ UsernameColumn, EmailColumn ]

usersSchema :: Schema Two UsersSchema
usersSchema = usernameColumn :| emailColumn :| EndSchema

type UsersTable = '( "users", UsersSchema )

usersTable :: Table UsersTable
usersTable = table

type TestDatabase = '[ UsersTable ]

makeSelectEmail
    :: forall alias .
       ( KnownSymbol alias )
    => Proxy alias
    -> T.Text
    -> Relation PostgresUniverse TestDatabase alias '[EmailColumn]
makeSelectEmail _ username = Base usersTable Proxy selection projection condition
  where
    selection :: Select One '[ '(alias, "email", T.Text) ]
    selection = emailColumn :+> EndSelect
    projection = emailColumn :| EndProject
    condition = col (Proxy :: Proxy '(alias, "username")) .==. lit username .||. false .&&. true

makeInsert
    :: T.Text
    -> T.Text
    -> Insert PostgresUniverse TestDatabase UsersTable
makeInsert username email = Insert usersTable row
  where
    row =   (fromColumnAndValue usernameColumn username)
        :&| (fromColumnAndValue emailColumn email)
        :&| EndRow

makeUpdate
    :: T.Text
    -> T.Text
    -> Update
           PostgresUniverse
           TestDatabase
           UsersTable
           '[ EmailColumn ]
           '[ '[ '[ '(T.Text, Just '("users", "username")), '(T.Text, Nothing) ] ] ]
makeUpdate username email = Update usersTable projection condition row
  where
    projection = emailColumn :| EndProject
    row = (fromColumnAndValue emailColumn email) :&| EndRow
    condition = col (Proxy :: Proxy '("users", "username")) .==. lit username .||. false .&&. true

makeDelete
    :: T.Text
    -> Delete
           PostgresUniverse
           TestDatabase
           UsersTable
           '[ '[ '[ '(T.Text, Just '("users", "username")), '(T.Text, Nothing) ] ] ]
makeDelete username = Delete usersTable condition
  where
    condition = col (Proxy :: Proxy '("users", "username")) .==. lit username .||. false .&&. true

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
    let username = args !! 0
        proxy :: Proxy (PostgresInterpreter IO)
        proxy = Proxy
        term :: RelationalF PostgresUniverse TestDatabase [Row '[EmailColumn]]
        term = rfrelation $ makeSelectEmail (Proxy :: Proxy "users") username
    in  do outcome <- runPostgresT (defaultConnectInfo { connectUser="alex" }) id id id (iterM (interpreter proxy) (liftF term))
           print outcome

mainInsert args =
    let username = args !! 0
        email = args !! 1
        proxy :: Proxy (PostgresInterpreter IO)
        proxy = Proxy
        term :: RelationalF PostgresUniverse TestDatabase ()
        term = rfinsert $ makeInsert username email
    in  runPostgresT (defaultConnectInfo { connectUser="alex" }) id id id (iterM (interpreter proxy) (liftF term))

mainUpdate args =
    let username = args !! 0
        email = args !! 1
        proxy :: Proxy (PostgresInterpreter IO)
        proxy = Proxy
        term :: RelationalF PostgresUniverse TestDatabase ()
        term = rfupdate $ makeUpdate username email
    in  runPostgresT (defaultConnectInfo { connectUser="alex" }) id id id (iterM (interpreter proxy) (liftF term))

mainDelete args =
    let username = args !! 0
        proxy :: Proxy (PostgresInterpreter IO)
        proxy = Proxy
        term :: RelationalF PostgresUniverse TestDatabase ()
        term = rfdelete $ makeDelete username
    in  runPostgresT (defaultConnectInfo { connectUser="alex" }) id id id (iterM (interpreter proxy) (liftF term))
