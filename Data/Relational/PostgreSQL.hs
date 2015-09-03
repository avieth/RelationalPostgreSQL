{-|
Module      : Data.Relational.PostgreSQL
Description : PostgreSQL-simple driver for Relational.
Copyright   : (c) Alexander Vieth, 2015
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)

TODO import Database.PostgreSQL.Simple.Types to obtain the Query constructor,
then use ByteString builders rather than string concatenation to compose the
query strings.

-}

{-# LANGUAGE AutoDeriveTypeable #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}

module Data.Relational.PostgreSQL (

    PostgresInterpreter(..)
  , PostgresT
  , Universe(..)
  , PostgresUniverse
  , runPostgresT

  ) where

import GHC.TypeLits (Symbol, symbolVal, KnownSymbol)
import Control.Applicative
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Reader
import Control.Monad.FInterpreter
import Data.TypeNat.Nat
import Data.Proxy
import Data.List (intersperse)
import Data.String (fromString)
import qualified Database.PostgreSQL.Simple as P
import qualified Database.PostgreSQL.Simple.Types as PT
import qualified Database.PostgreSQL.Simple.ToField as PTF
import qualified Database.PostgreSQL.Simple.ToRow as PTR
import qualified Database.PostgreSQL.Simple.FromField as PFF
import qualified Database.PostgreSQL.Simple.FromRow as PFR
import qualified Data.Text as T
import qualified Data.ByteString as BS
import Data.Int (Int64)
import Data.Time.Calendar
import Data.Time.Clock
import Data.UUID hiding (fromString)
import Data.Relational
import Data.Relational.TypeList
import Data.Relational.Universe
import Data.Relational.Interpreter
import Data.Relational.RelationalF

data PostgresUniverse

instance (FromAndToField t) => InRelationalUniverse PostgresUniverse t where
    type RelationalUniverseType PostgresUniverse t = t
    toUniverse _ = id
    fromUniverse _ _ = Just

class (PTF.ToField t, PFF.FromField t) => FromAndToField t
instance (PTF.ToField t, PFF.FromField t) => FromAndToField t

fromAndToFieldImpliesToField :: HasConstraint FromAndToField t -> HasConstraint PTF.ToField t
fromAndToFieldImpliesToField x = case x of HasConstraint -> HasConstraint

fromAndToFieldImpliesFromField :: HasConstraint FromAndToField t -> HasConstraint PFF.FromField t
fromAndToFieldImpliesFromField x = case x of HasConstraint -> HasConstraint

instance RelationalUniverse PostgresUniverse where
    type RelationalUniverseConstraint PostgresUniverse = FromAndToField

data PostgresInterpreter (m :: * -> *) = PostgresInterpreter

newtype PostgresT m a = PostgresT {
    exitPostgresT :: ReaderT P.Connection m a
  } deriving (Functor, Applicative, Monad, MonadTrans, MonadIO)

instance IsMonadTransformer PostgresT where
    monadProof = MonadProof

runPostgresT
    :: forall m n a b .
       ( Monad n )
    => P.ConnectInfo
    -> (m a -> n b)
    -> (forall a . n a -> IO a)
    -> (forall a . IO a -> n a)
    -> PostgresT m a
    -> n b
runPostgresT connInfo makeN makeIO liftIO pm = do
    conn <- liftIO $ P.connect connInfo
    liftIO (P.withTransaction conn (makeIO (makeN (runReaderT (exitPostgresT pm) conn))))

instance FTrans PostgresT where
    transInterp interp term = PostgresT . ReaderT $ \conn ->
        let q = fmap ((flip runReaderT) conn . exitPostgresT) term
        in  interp q

instance
    ( MonadIO m
    , Functor m
    , Every (InRelationalUniverse PostgresUniverse) (Snds (Concat (Snds db)))
    , InterpreterRelationConstraint (PostgresInterpreter m) db
    , InterpreterInsertConstraint (PostgresInterpreter m) db
    , InterpreterUpdateConstraint (PostgresInterpreter m) db
    , InterpreterDeleteConstraint (PostgresInterpreter m) db
    , Unique (TableNames db)
    ) => FInterpreter PostgresT m (RelationalF PostgresUniverse db)
  where
    finterpret = interpreter (Proxy :: Proxy (PostgresInterpreter m))

instance (Functor m, MonadIO m) => RelationalInterpreter (PostgresInterpreter m) where

    type Universe (PostgresInterpreter m) = PostgresUniverse

    type InterpreterMonad (PostgresInterpreter m) = PostgresT m

    type InterpreterRelationConstraint (PostgresInterpreter m) db = ()
    type InterpreterInsertConstraint (PostgresInterpreter m) db = ()
    type InterpreterUpdateConstraint (PostgresInterpreter m) db = ()
    type InterpreterDeleteConstraint (PostgresInterpreter m) db = ()

    interpretRelation proxyPI (proxyDB :: Proxy db) (relation :: Relation PostgresUniverse db tableName projected) =

        let (query, parameters) = relationQueryAndParameters relation

            makeRow :: HList (RelationalUniverseTypes PostgresUniverse (Snds projected)) -> [Row projected]
            makeRow hlist = case relationProjectionIsInUniverse relation of
                EveryConstraint -> case relationProjectionIsTypeList relation of
                    HasConstraint -> case inRelationalUniverseImpliesRelationalUniverseConstraint proxyU (Proxy :: Proxy (Snds projected)) of
                        EveryConstraint -> case relationalUniverseTypesIsTypeList proxyU (Proxy :: Proxy (Snds projected)) HasConstraint of
                            HasConstraint -> case typeListEvery fromAndToFieldImpliesFromField EveryConstraint :: EveryConstraint PFF.FromField (RelationalUniverseTypes PostgresUniverse (Snds projected)) of
                                EveryConstraint -> case convertToRow proxyU projection hlist of
                                    Nothing -> []
                                    Just x -> [x]

            doQuery :: P.Connection -> IO [HList (RelationalUniverseTypes PostgresUniverse (Snds projected))]
            doQuery = case relationProjectionIsInUniverse relation of
                EveryConstraint -> case relationProjectionIsTypeList relation of
                    HasConstraint -> case inRelationalUniverseImpliesRelationalUniverseConstraint proxyU (Proxy :: Proxy (Snds projected)) of
                        EveryConstraint -> case relationalUniverseTypesIsTypeList proxyU (Proxy :: Proxy (Snds projected)) HasConstraint of
                            HasConstraint -> case typeListEvery fromAndToFieldImpliesFromField EveryConstraint :: EveryConstraint PFF.FromField (RelationalUniverseTypes PostgresUniverse (Snds projected)) of
                                EveryConstraint -> case parameters of
                                    SomeToRow ps -> \conn -> P.query conn (fromString query) ps

            projection :: Project (Length projected) projected
            projection = case relationProjectionIsProjection relation of
                HasConstraint2 -> project Proxy

            proxyU :: Proxy PostgresUniverse
            proxyU = Proxy

        in  PostgresT $ do
                conn <- ask
                results <- liftIO (doQuery conn)
                let rows = results >>= makeRow
                return rows

    interpretInsert proxyPI (proxyDB :: Proxy db) insert@(Insert table (row :: Row schema)) =
        let statement :: P.Query
            statement = fromString (makeInsertStatement insert)

            hlist :: HList (Snds schema)
            hlist = case rowToHListProof (insertRow insert) of
                HasConstraint -> rowToHList (insertRow insert)

            parameters :: HList (RelationalUniverseTypes PostgresUniverse (Snds schema))
            parameters = allToUniverse proxyU hlist

            -- To do the query we must show that Snds schema (types in the row to
            -- be inserted) all have PTF.ToField.
            -- To do this, we use the fact that each of these are in the
            -- PostgresUniverse, and that everything in the PostgresUniverse is
            -- PTF.ToField.
            doQuery :: P.Connection -> IO Int64
            doQuery = case inRelationalUniverseImpliesRelationalUniverseConstraint proxyU (Proxy :: Proxy (Snds schema)) of
                EveryConstraint -> case relationalUniverseTypesIsTypeList proxyU (Proxy :: Proxy (Snds schema)) HasConstraint of
                    HasConstraint -> case typeListEvery fromAndToFieldImpliesToField EveryConstraint :: EveryConstraint PTF.ToField (RelationalUniverseTypes PostgresUniverse (Snds schema)) of
                        EveryConstraint -> \conn -> P.execute conn statement parameters

            proxyU :: Proxy PostgresUniverse
            proxyU = Proxy

        in  PostgresT $ do
                conn <- ask
                liftIO (doQuery conn)
                return ()

    interpretUpdate proxyPI (proxyDB :: Proxy db) update@(Update table project (condition :: Condition conditioned) (row :: Row projected)) =

        let statement :: P.Query
            statement = fromString (makeUpdateStatement update)

            conditionParameters :: HList (RelationalUniverseTypes PostgresUniverse (ConditionTypeList conditioned))
            conditionParameters = allToUniverse proxyU (conditionValues (updateCondition update))

            hlist :: HList (Snds projected)
            hlist = case rowToHListProof (updateColumns update) of
                HasConstraint -> rowToHList (updateColumns update)

            assignmentParameters :: HList (RelationalUniverseTypes PostgresUniverse (Snds projected))
            assignmentParameters = allToUniverse proxyU hlist

            -- Twice the amount of proofs as for the insert case, as we must
            -- prove ToField for condition, and assignment parameters.
            doQuery :: P.Connection -> IO Int64
            doQuery = case inRelationalUniverseImpliesRelationalUniverseConstraint proxyU (Proxy :: Proxy (Snds projected)) of
                EveryConstraint -> case relationalUniverseTypesIsTypeList proxyU (Proxy :: Proxy (Snds projected)) HasConstraint of
                    HasConstraint -> case typeListEvery fromAndToFieldImpliesToField EveryConstraint :: EveryConstraint PTF.ToField (RelationalUniverseTypes PostgresUniverse (Snds projected)) of
                        EveryConstraint -> case inRelationalUniverseImpliesRelationalUniverseConstraint proxyU (Proxy :: Proxy (ConditionTypeList conditioned)) of
                            EveryConstraint -> case relationalUniverseTypesIsTypeList proxyU (Proxy :: Proxy (ConditionTypeList conditioned)) HasConstraint of
                                HasConstraint -> case typeListEvery fromAndToFieldImpliesToField EveryConstraint :: EveryConstraint PTF.ToField (RelationalUniverseTypes PostgresUniverse (ConditionTypeList conditioned)) of
                                    EveryConstraint -> \conn -> P.execute conn statement (assignmentParameters PT.:. conditionParameters)

            proxyU :: Proxy PostgresUniverse
            proxyU = Proxy

        in  PostgresT $ do
                conn <- ask
                liftIO (doQuery conn)
                return ()

    interpretDelete proxyU (proxyDB :: Proxy db) delete@(Delete table (condition :: Condition conditioned)) =

        let statement :: P.Query
            statement = fromString (makeDeleteStatement delete)

            parameters :: HList (RelationalUniverseTypes PostgresUniverse (ConditionTypeList conditioned))
            parameters = allToUniverse proxyU (conditionValues (deleteCondition delete))

            doQuery :: P.Connection -> IO Int64
            doQuery = case inRelationalUniverseImpliesRelationalUniverseConstraint proxyU (Proxy :: Proxy (ConditionTypeList conditioned)) of
                EveryConstraint -> case relationalUniverseTypesIsTypeList proxyU (Proxy :: Proxy (ConditionTypeList conditioned)) HasConstraint of
                    HasConstraint -> case typeListEvery fromAndToFieldImpliesToField EveryConstraint :: EveryConstraint PTF.ToField (RelationalUniverseTypes PostgresUniverse (ConditionTypeList conditioned)) of
                        EveryConstraint -> \conn -> P.execute conn statement parameters

            proxyU :: Proxy PostgresUniverse
            proxyU = Proxy

        in  PostgresT $ do
                conn <- ask
                liftIO (doQuery conn)
                return ()

-- | Wrapper over the PostgreSQL-simple RowParser, so that we can make it
--   work with HLists. The type parameter is a list of types.
newtype RowParserL ts = RowParserL {
    runRowParserL :: PFR.RowParser (HList ts)
  }

rowParserCons :: PFR.RowParser t -> RowParserL ts -> RowParserL (t ': ts)
rowParserCons rp rpl = RowParserL (ConsHList <$> rp <*> (runRowParserL rpl))

-- | To make a FromRow for an HList, we use the typeListFoldr mechanism from
--   the TypeList class to produce a RowParserL (necessary in order to fit the
--   type signature of typeListFoldr) and then we use that to produce the
--   RowParser proper.
instance (TypeList types, Every PFF.FromField types) => PFR.FromRow (HList types) where
    fromRow = runRowParserL (typeListBuild proxyList proxyConstraint f (RowParserL (pure EmptyHList)))
      where
        proxyList :: Proxy types
        proxyList = Proxy
        proxyConstraint :: Proxy PFF.FromField
        proxyConstraint = Proxy
        f :: forall t ts . PFF.FromField t => Proxy t -> RowParserL ts -> RowParserL (t ': ts)
        f proxyT rpl = rowParserCons PFR.field rpl

instance (Every PTF.ToField types) => PTR.ToRow (HList types) where
    toRow lst = case lst of
        EmptyHList -> []
        ConsHList v rest -> PTF.toField v : PTR.toRow rest

makeInsertStatement :: Insert universe db '(sym, schema) -> String
makeInsertStatement insert =
    concat
    [ "INSERT INTO "
    , tableName table
    , " ("
    , columns schema
    , ") VALUES ("
    , valuePlaceholders schema
    , ")"
    ]

  where

    table = insertTable insert

    schema = tableSchema table

    columns = concat . intersperse "," . makeInsertColumns

    valuePlaceholders = concat . intersperse "," . makeSchemaFields

    makeInsertColumns :: Schema n ss -> [String]
    makeInsertColumns sch = case sch of
        EmptySchema -> []
        ConsSchema col rest -> columnName col : makeInsertColumns rest

    makeSchemaFields :: Schema n ss -> [String]
    makeSchemaFields sch = case sch of
        EmptySchema -> []
        ConsSchema _ rest -> "?" : makeSchemaFields rest

makeDeleteStatement :: Delete universe db '(sym, schema) conditioned -> String
makeDeleteStatement delete =
    concat
    [ "DELETE FROM "
    , tableName (deleteTable delete)
    , " WHERE "
    , conditionClause
    ]
  where
    conditionClause = makeConditionClause (deleteCondition delete)

makeUpdateStatement :: Update universe db '(sym, schema) projected conditioned -> String
makeUpdateStatement update =
    concat
    [ "UPDATE "
    , tableName table
    , " SET "
    , assignments (updateProject update)
    , " WHERE "
    , makeConditionClause (updateCondition update)
    ]

  where

    table = updateTable update

    assignments = concat . intersperse "," . makeAssignments

    makeAssignments :: Project n ps -> [String]
    makeAssignments prj = case prj of
        EndProject -> []
        ConsProject col rest -> (concat [columnName col, " = ?"]) : (makeAssignments rest)

data SomeToField where
    SomeToField :: PTF.ToField f => f -> SomeToField

instance PTF.ToField SomeToField where
    toField x = case x of
        SomeToField y -> PTF.toField y

data SomeToRow where
    SomeToRow :: PTR.ToRow r => r -> SomeToRow

relationQueryAndParameters
    :: forall m db projected tableName .
       ()
    => Relation PostgresUniverse db tableName projected
    -> (String, SomeToRow)
relationQueryAndParameters term = case term of

    Base table proxy select project (condition :: Condition condition) ->

        let -- The query string, with ? placeholders for values.
            -- The actual values come from the condition only.
            query :: String
            query = makeTableClause (Proxy :: Proxy tableName) table proxy select project condition

            -- These are the parameters which shall be substituted for the ?
            -- placeholders in the query string.
            parameters :: HList (RelationalUniverseTypes PostgresUniverse (ConditionTypeList condition))
            parameters = allToUniverse proxyU (conditionValues (condition))

            proxyParameters :: Proxy (ConditionTypeList condition)
            proxyParameters = Proxy

        -- Here we have to convince GHC about a bunch of obvious things:
        -- - Since every one of the condition types is in the universe, every
        --   one of them satisfies the universe constraint (FromAndToField).
        -- - The type RelationalUniverseTypes (ConditionTypeList ts) satisfies
        --   the TypeList constraint.
        -- - Since every element of (RelationalUniverseTypes (ConditionTypeList ts))
        --   satisfies FromAndToField, every one of them also satisfies
        --   PTF.ToField (a superclass of FromAndToField).
        -- With that out of the way, we can create a SomeToRow of parameters.
        in  case inRelationalUniverseImpliesRelationalUniverseConstraint proxyU proxyParameters of
                EveryConstraint -> case relationalUniverseTypesIsTypeList proxyU (Proxy :: Proxy (ConditionTypeList condition)) HasConstraint of
                    HasConstraint -> case typeListEvery fromAndToFieldImpliesToField EveryConstraint :: EveryConstraint PTF.ToField (RelationalUniverseTypes PostgresUniverse (ConditionTypeList condition)) of
                        EveryConstraint -> (query, SomeToRow parameters)

    Literal (table :: LiteralTable schema) proxy select project (condition :: Condition condition) ->

        let query :: String
            query = makeLiteralTableClause (Proxy :: Proxy tableName) table proxy select project condition

            valueHList :: [HList (Snds schema)]
            valueHList = case table of
                LiteralTable rows -> fmap rowHList rows

            valueParameters :: [HList (RelationalUniverseTypes PostgresUniverse (Snds schema))]
            valueParameters = fmap (allToUniverse proxyU) valueHList

            conditionParameters :: HList (RelationalUniverseTypes PostgresUniverse (ConditionTypeList condition))
            conditionParameters = allToUniverse proxyU (conditionValues (condition))

            -- The literal table has, in addition to the condition parameters,
            -- the value parameters which make up the data in the literal
            -- table. These too are substituted via ? placeholders.
            -- We do not know statically how many of them we shall have (the
            -- literal table has a [] of rows) so here we get a [] of things
            -- which can be dumped to fields.
            makeSomeToField
                :: forall ts .
                   EveryConstraint PTF.ToField ts
                -> HList ts
                -> [SomeToField]
            makeSomeToField every hlist = case hlist of
                HNil -> []
                (x :: t) :> (rest :: HList rest) -> case every :: EveryConstraint PTF.ToField (t ': rest) of
                    EveryConstraint -> SomeToField x : makeSomeToField (EveryConstraint :: EveryConstraint PTF.ToField rest) rest

            proxyValues :: Proxy (Snds schema)
            proxyValues = Proxy

            proxyConditions :: Proxy (ConditionTypeList condition)
            proxyConditions = Proxy

        -- Compare with the work done in the case for Base above.
        -- Here we do twice the work, since we must prove things about the
        -- condition types and also the value types (to fill in the literal
        -- table).
        in  case inRelationalUniverseImpliesRelationalUniverseConstraint proxyU proxyValues of
                EveryConstraint -> case inRelationalUniverseImpliesRelationalUniverseConstraint proxyU proxyConditions of
                    EveryConstraint -> case relationalUniverseTypesIsTypeList proxyU proxyValues HasConstraint of
                        HasConstraint -> case relationalUniverseTypesIsTypeList proxyU proxyConditions HasConstraint of
                            HasConstraint -> case typeListEvery fromAndToFieldImpliesToField EveryConstraint :: EveryConstraint PTF.ToField (RelationalUniverseTypes PostgresUniverse (Snds schema)) of
                                EveryConstraint -> case typeListEvery fromAndToFieldImpliesToField EveryConstraint :: EveryConstraint PTF.ToField (RelationalUniverseTypes PostgresUniverse (ConditionTypeList condition)) of
                                    EveryConstraint -> (query, SomeToRow $ leftParameters PT.:. rightParameters)
                                      where
                                        leftParameters = valueParameters >>= makeSomeToField EveryConstraint
                                        rightParameters = conditionParameters

    Join (leftRelation :: Relation PostgresUniverse db leftAlias leftSchema) (rightRelation :: Relation PostgresUniverse db rightAlias rightSchema) proxySchemaLength select project condition ->
        let (lquery, lparams) = relationQueryAndParameters leftRelation
            (rquery, rparams) = relationQueryAndParameters rightRelation
        in  case (lparams, rparams) of
                (SomeToRow l, SomeToRow r) -> (
                        concat [
                              "SELECT "
                            , makeProjectionClause (select, project)
                            , " FROM ("
                            , lquery
                            , ") AS "
                            , leftAlias 
                            , " LEFT JOIN ("
                            , rquery
                            , ") AS "
                            , rightAlias
                            , " ON "
                            , makeConditionClause condition
                            ]
                      , SomeToRow (l PT.:. r)
                      )

      where

        leftAlias = case relationKnownSymbol leftRelation of
            HasConstraint -> symbolVal (Proxy :: Proxy leftAlias)
        rightAlias = case relationKnownSymbol rightRelation of
            HasConstraint -> symbolVal (Proxy :: Proxy rightAlias)

    Intersection left right ->
        let (lquery, lparams) = relationQueryAndParameters left
            (rquery, rparams) = relationQueryAndParameters right
        in  case (lparams, rparams) of
                (SomeToRow l, SomeToRow r) ->
                    (concat [lquery, " INTERSECT ", rquery], SomeToRow (l PT.:. r))

    Union left right ->
        let (lquery, lparams) = relationQueryAndParameters left
            (rquery, rparams) = relationQueryAndParameters right
        in  case (lparams, rparams) of
                (SomeToRow l, SomeToRow r) ->
                    (concat [lquery, " UNION ", rquery], SomeToRow (l PT.:. r))

  where

    proxyU :: Proxy PostgresUniverse
    proxyU = Proxy

makeRelationClause
    :: forall universe db tableAlias projection . 
       Relation universe db tableAlias projection
    -> String
makeRelationClause relation = case relation of

    Base table proxy select project condition ->
        makeTableClause (Proxy :: Proxy tableAlias) table proxy select project condition

    Literal table proxy select project condition ->
        makeLiteralTableClause (Proxy :: Proxy tableAlias) table proxy select project condition

    Join (leftRelation :: Relation universe db leftAlias leftSchema) (rightRelation :: Relation universe db rightAlias rightSchema) proxySchemaLength select project condition -> concat [
          "SELECT "
        , makeProjectionClause (select, project)
        , " FROM ("
        , makeRelationClause leftRelation
        , ") AS "
        , leftAlias 
        , " LEFT JOIN ("
        , makeRelationClause rightRelation
        , ") AS "
        , rightAlias
        , " ON "
        , makeConditionClause condition
        ]

      where

        leftAlias = case relationKnownSymbol leftRelation of
            HasConstraint -> symbolVal (Proxy :: Proxy leftAlias)
        rightAlias = case relationKnownSymbol rightRelation of
            HasConstraint -> symbolVal (Proxy :: Proxy rightAlias)

    Intersection rel1 rel2 -> concat [
          makeRelationClause rel1
        , " INTERSECT "
        , makeRelationClause rel2
        ]

    Union rel1 rel2 -> concat [
          makeRelationClause rel1
        , " UNION "
        , makeRelationClause rel2
        ]

{-
test1 :: Relation (PostgresUniverse) db "foobar" '[ '("foo", Int) ]
test1 = Literal
    (LiteralTable [] :: LiteralTable '[ '("bar", Int) ])
    (Proxy :: Proxy One)
    (column :+> EndSelect :: Select One '[ '("foobar", "bar", Int) ])
    (column :| EndProject :: Project One '[ '("foo", Int) ]) true

test2 :: Relation (PostgresUniverse) db "table_alias_1" '[ '("foo", Bool), '("bar", Int) ]
test2 = Literal
    (LiteralTable [(field 1 :&| field True :&| EndRow)] :: LiteralTable '[ '("a", Int), '("b", Bool) ])
    (Proxy :: Proxy Two)
    (column :+> column :+> EndSelect :: Select Two '[ '("table_alias_1", "b", Bool), '("table_alias_1", "a", Int) ])
    (column :| column :| EndProject :: Project Two '[ '("foo", Bool), '("bar", Int) ])
    true

test3 :: Relation (PostgresUniverse) '[ '("my_table", '[ '("a", Int), '("b", Bool), '("c", T.Text) ]) ] "table_alias_2" '[ '("foo", Bool), '("bar", Int) ]
test3 = Base
    (Table (Proxy :: Proxy "my_table") (Proxy :: Proxy '[ '("a", Int), '("b", Bool), '("c", T.Text) ]))
    (Proxy :: Proxy Two)
    (column :+> column :+> EndSelect :: Select Two '[ '("table_alias_2", "b", Bool), '("table_alias_2", "a", Int) ])
    (column :| column :| EndProject :: Project Two '[ '("foo", Bool), '("bar", Int) ])
    true

test4 :: Relation (PostgresUniverse) '[ '("my_table", '[ '("a", Int), '("b", Bool), '("c", T.Text)]) ] "joined" '[ '("id", Int) ]
test4 = Join
    test2
    test3
    Proxy
    (column :+> EndSelect :: Select One '[ '("table_alias_2", "bar", Int) ])
    (column :| EndProject :: Project One '[ '("id", Int) ])
    true
-}

makeTableClause
    :: forall tableAlias name schema n select project condition .
       ( KnownSymbol tableAlias
       , Length select ~ S n
       )
    => Proxy tableAlias
    -> Table '(name, schema)
    -> Proxy (S n)
    -> Select (Length select) select
    -> Project (Length select) project
    -> Condition condition
    -> String
makeTableClause aliasProxy tbl proxy select project condition = case tbl of
    Table tableNameProxy schemaProxy -> concat [
          "SELECT "
        , makeProjectionClause (select, project)
        , " FROM "
        , symbolVal tableNameProxy
        , " AS "
        , symbolVal aliasProxy
        , " WHERE "
        , makeConditionClause condition
        ]

makeLiteralTableClause
    :: forall tableAlias schema n select project condition .
       ( KnownSymbol tableAlias
       , Length select ~ S n
       )
    => Proxy tableAlias
    -> LiteralTable schema
    -> Proxy (S n)
    -> Select (Length select) select
    -> Project (Length select) project
    -> Condition condition
    -> String
makeLiteralTableClause aliasProxy tbl lengthProxy select project condition = case tbl of
    LiteralTable rows -> case rows of
        [] -> concat [
              "SELECT "
            , makeNullProjectionClause project
            , " LIMIT 0"
            ]
        (r : rs) -> concat [
              "SELECT "
            , makeProjectionClause (select, project)
            , " FROM "
            , makeRowsValuesClause r rs
            , " AS "
            --, makeValuesAliasClause aliasProxy select
            , makeValuesAliasClause aliasProxy (schema (Proxy :: Proxy schema))
            , " WHERE "
            , makeConditionClause condition
            ]

makeValuesAliasClause :: KnownSymbol name => Proxy name -> Schema (Length schema) schema -> String
makeValuesAliasClause table schema = concat [
      symbolVal table
    , "("
    , concat (intersperse ", " (makeValuesAliasColumnsClauseList schema))
    , ")"
    ]

makeValuesAliasColumnsClauseList :: Schema (Length schema) schema -> [String]
makeValuesAliasColumnsClauseList schema = case schema of
    -- GHC claims these patterns overlap. Bug?
    EndSchema -> []
    ConsSchema col rest -> columnName col : makeValuesAliasColumnsClauseList rest

-- Row and list of Rows because we can't make a values clause with 0 rows;
-- it's not legal SQL as far as I know.
-- 0-row literal tables are handled separately, by selecting NULL columns and
-- limiting to 0.
makeRowsValuesClause :: Row schema -> [Row schema] -> String
makeRowsValuesClause row otherRows = concat [
      "(VALUES "
    , concat (intersperse ", " (makeRowsValuesClauseList (row : otherRows)))
    , ")"
    ]

makeRowsValuesClauseList :: [Row schema] -> [String]
makeRowsValuesClauseList = fmap makeRowsValuesClauseSingle

makeRowsValuesClauseSingle :: Row schema -> String
makeRowsValuesClauseSingle row = concat [
      "("
    , concat (intersperse ", " (makeRowsValuesClauseSingleNoParens row))
    , ")"
    ]

makeRowsValuesClauseSingleNoParens :: Row schema -> [String]
makeRowsValuesClauseSingleNoParens row = case row of
    EmptyRow -> []
    ConsRow field rest -> "?" : makeRowsValuesClauseSingleNoParens rest

-- | Make the clause which goes between SELECT and FROM, picking columns from
--   a Select and renaming them according to a Project.
--
--   TODO constrain types in ss and ps to be compatible...
--   Coercible on the type components?
makeProjectionClause :: (Select (S n) ss, Project (S n) ps) -> String
makeProjectionClause = concat . intersperse ", " . makeSelectFields
  where
    makeSelectFields :: (Select (S n) ss, Project (S n) ps) -> [String]
    makeSelectFields ps = case ps of
        (ConsSelect (tableName, col) rest, ConsProject col' rest') -> concat [
              symbolVal tableName
            , "."
            , columnName col
            , " AS "
            , columnName col'
          ]
          : case (rest, rest') of
                (EndSelect, EndProject) -> []
                (ConsSelect _ _, ConsProject _ _) -> makeSelectFields (rest, rest')

makeNullProjectionClause :: Project (S n) ps -> String
makeNullProjectionClause = concat . intersperse ", " . makeProjectFields
  where
    makeProjectFields :: Project (S n) ps -> [String]
    makeProjectFields ps = case ps of
        ConsProject col rest -> concat [
              "NULL as "
            , columnName col
            ]
            : case rest of
                  EndProject -> []
                  ConsProject _ _ -> makeProjectFields rest

-- | Make the clause which goes after WHERE, leaving ? holes for literals.
makeConditionClause :: Condition css -> String
makeConditionClause constr = case constr of
    AndCondition disjunction rest -> case disjunction of
        -- We're careful to identify disjunctions with no terms, and replace
        -- them with true, otherwise the entire conjunction would always turn
        -- out false.
        AlwaysFalse -> "TRUE"
        OrCondition _ _ -> concat ["(", makeDisjunctionClause disjunction, " ) AND ", makeConditionClause rest]
    AlwaysTrue -> "TRUE"

makeDisjunctionClause :: NonEmpty cs => ConditionDisjunction cs -> String
makeDisjunctionClause disj = case disj of
    OrCondition terminal rest -> case rest of
        OrCondition _ _ -> concat ["(", makeTerminalClause terminal, ") OR ", makeDisjunctionClause rest]
        AlwaysFalse -> concat ["(", makeTerminalClause terminal, ")"]

makeTerminalClause :: ConditionTerminal t -> String
makeTerminalClause term = case term of
    BoolCondition val -> makeValueClause val
    NullCondition val -> concat [makeValueClause val, "IS NULL"]
    EqCondition val1 val2 -> concat [makeValueClause val1, " = ", makeValueClause val2]
    LtCondition val1 val2 -> concat [makeValueClause val1, " < ", makeValueClause val2]
    GtCondition val1 val2 -> concat [makeValueClause val1, " > ", makeValueClause val2]
    NotCondition x -> concat ["NOT (", makeTerminalClause x, ")"]

makeValueClause :: ConditionValue t cols -> String
makeValueClause v = case v of
    LiteralValue x -> "?"
    ColumnValue tableName col -> concat [symbolVal tableName, ".", columnName col]
