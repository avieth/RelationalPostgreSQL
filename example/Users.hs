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

type UsernameColumn = '( "username", T.Text )

usernameColumn :: Column UsernameColumn
usernameColumn = column

type EmailColumn = '( "email", T.Text )

emailColumn :: Column EmailColumn
emailColumn = column

type UsersSchema = '[ UsernameColumn, EmailColumn ]

usersSchema :: Schema UsersSchema
usersSchema = usernameColumn :| emailColumn :| EndSchema

type UsersTable = '( "users", UsersSchema )

usersTable :: Table UsersTable
usersTable = table usersSchema

type TestDatabase = '[ UsersTable ]

makeSelectEmail :: T.Text -> Relational TestDatabase [Row '[EmailColumn]]
makeSelectEmail username = rfselect (Select usersTable projection condition)
  where
    projection = emailColumn :+| EndProject
    condition = usernameColumn .==. username .||. false .&&. true

makeInsert :: T.Text -> T.Text -> Relational TestDatabase ()
makeInsert username email = rfinsert (Insert usersTable row)
  where
    row =   (fromColumnAndValue usernameColumn username)
        :&| (fromColumnAndValue emailColumn email)
        :&| EndRow

makeUpdate :: T.Text -> T.Text -> Relational TestDatabase ()
makeUpdate username email = rfupdate (Update usersTable projection condition row)
  where
    projection = emailColumn :+| EndProject
    row = (fromColumnAndValue emailColumn email) :&| EndRow
    condition = usernameColumn .==. username .||. false .&&. true

makeDelete :: T.Text -> Relational TestDatabase ()
makeDelete username = rfdelete (Delete usersTable condition)
  where
    condition = usernameColumn .==. username .||. false .&&. true

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
        term = iterM (interpreter proxy) (makeSelectEmail username)
    in  do outcome <- runPostgresT (defaultConnectInfo { connectUser="alex" }) id term
           print outcome

mainInsert args =
    let username = args !! 0
        email = args !! 1
        proxy :: Proxy (PostgresInterpreter IO)
        proxy = Proxy
        term = iterM (interpreter proxy) (makeInsert username email)
    in  runPostgresT (defaultConnectInfo { connectUser="alex" }) id term

mainUpdate args =
    let username = args !! 0
        email = args !! 1
        proxy :: Proxy (PostgresInterpreter IO)
        proxy = Proxy
        term = iterM (interpreter proxy) (makeUpdate username email)
    in  runPostgresT (defaultConnectInfo { connectUser="alex" }) id term

mainDelete args =
    let username = args !! 0
        proxy :: Proxy (PostgresInterpreter IO)
        proxy = Proxy
        term = iterM (interpreter proxy) (makeDelete username)
    in  runPostgresT (defaultConnectInfo { connectUser="alex" }) id term
