{-|
Module      : Data.Relational.PostgreSQL
Description : PostgreSQL-simple driver for Relational.
Copyright   : (c) Alexander Vieth, 2015
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
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

import Control.Applicative
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Reader
import Control.Monad.FInterpreter
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
import Data.Relational.Universe
import Data.Relational.Interpreter
import Data.Relational.RelationalF

data PostgresInterpreter (m :: * -> *) = PostgresInterpreter
type PostgresUniverse m = Universe (PostgresInterpreter m)

newtype PostgresT m a = PostgresT {
    exitPostgresT :: ReaderT P.Connection m a
  } deriving (Functor, Applicative, Monad, MonadTrans, MonadIO)

runPostgresT :: MonadIO m => P.ConnectInfo -> (forall a . m a -> IO a) -> PostgresT m a -> IO a
runPostgresT connInfo runner pm = do
    conn <- liftIO $ P.connect connInfo
    P.withTransaction conn (runner (runReaderT (exitPostgresT pm) conn))

instance FTrans PostgresT where
    transInterp interp term = PostgresT . ReaderT $ \conn ->
        let q = fmap ((flip runReaderT) conn . exitPostgresT) term
        in  interp q

instance
    ( MonadIO m
    , Functor m
    , Every (InUniverse (PostgresUniverse m)) (Snds (Concat (Snds db)))
    , InterpreterRelationConstraint (PostgresInterpreter m) db
    , InterpreterInsertConstraint (PostgresInterpreter m) db
    , InterpreterUpdateConstraint (PostgresInterpreter m) db
    , InterpreterDeleteConstraint (PostgresInterpreter m) db
    , Unique (TableNames db)
    ) => FInterpreter PostgresT m (RelationalF db)
  where
    finterpret = interpreter (Proxy :: Proxy (PostgresInterpreter m))

instance (Functor m, MonadIO m) => RelationalInterpreter (PostgresInterpreter m) where

    data Universe (PostgresInterpreter m) t where
      UText :: T.Text -> Universe (PostgresInterpreter m) t
      UBytes :: BS.ByteString -> Universe (PostgresInterpreter m) t
      UInt :: Int -> Universe (PostgresInterpreter m) t
      UDouble :: Double -> Universe (PostgresInterpreter m) t
      UBool :: Bool -> Universe (PostgresInterpreter m) t
      UDay :: Day -> Universe (PostgresInterpreter m) t
      UUUID :: UUID -> Universe (PostgresInterpreter m) t
      UUTCTime :: UTCTime -> Universe (PostgresInterpreter m) t
      UNullable :: Maybe (Universe (PostgresInterpreter m) t) -> Universe (PostgresInterpreter m) (Maybe t)

    type InterpreterMonad (PostgresInterpreter m) = PostgresT m

    type InterpreterRelationConstraint (PostgresInterpreter m) db =
             ( Every PTF.ToField (Fmap (PostgresUniverse m) (Snds (Concat (Snds db))))
             , Every PFF.FromField (Fmap (PostgresUniverse m) (Snds (Concat (Snds db))))
             , TypeList (Snds (Concat (Snds db)))
             )

    interpretRelation proxyPI (proxyDB :: Proxy db) (relation :: Relation db projected) =

        let (query, parameters) = relationQueryAndParameters proxyU relation

            doQuery :: P.Connection -> IO [HList (Fmap (PostgresUniverse m) (Snds projected))]
            doQuery = case (parameters, everyFromField, typeListProof2) of
                (SomeToRow parameters', EveryConstraint, HasConstraint) ->
                      \conn -> P.query conn (fromString query) parameters'

            project :: Project projected
            project = case relationParameterIsProjection relation of
                HasConstraint -> projection Proxy

            makeRow hlist = case typeListProof1 of
                HasConstraint -> case convertToRow proxyU proxyDB project hlist of
                    Nothing -> []
                    Just x -> [x]

            proxyU :: Proxy (Universe (PostgresInterpreter m))
            proxyU = Proxy

            containsFmapProof = fmapContainsProof proxyU proxyDBFlat proxyProjected

            everyFromField = case containsFmapProof of
                HasConstraint -> containsConstraint proxyFromField proxyDBU proxyProjectedU

            typeListProof1 = typeListContainsProof proxyDBFlat proxyProjected

            typeListProof2 = case typeListProof1 of
                HasConstraint -> typeListFmapProof proxyU proxyProjected

            proxyDBFlat :: Proxy (Snds (Concat (Snds db)))
            proxyDBFlat = Proxy

            proxyDBU :: Proxy (Fmap (PostgresUniverse m) (Snds (Concat (Snds db))))
            proxyDBU = Proxy

            proxyFromField :: Proxy PFF.FromField
            proxyFromField = Proxy

            proxyProjected :: Proxy (Snds projected)
            proxyProjected = Proxy

            proxyProjectedU :: Proxy (Fmap (PostgresUniverse m) (Snds projected))
            proxyProjectedU = Proxy

        in  PostgresT $ do
                conn <- ask
                results <- liftIO (doQuery conn)
                let rows = results >>= makeRow
                return rows

    type InterpreterInsertConstraint (PostgresInterpreter m) db =
             ( Every PTF.ToField (Fmap (PostgresUniverse m) (Snds (Concat (Snds db))))
             )

    interpretInsert proxyPI (proxyDB :: Proxy db) insert@(Insert table (row :: Row schema)) =
        let statement :: P.Query
            statement = fromString (makeInsertStatement insert)

            hlist :: HList (Snds schema)
            hlist = case rowToHListProof (insertRow insert) of
                HasConstraint -> rowToHList (insertRow insert)

            parameters :: HList (Fmap (PostgresUniverse m) (Snds schema))
            parameters = allToUniverse proxyU proxyDB hlist

            containsFmapProof = fmapContainsProof proxyU proxyDBFlat proxySchema

            everyToField = case containsFmapProof of
                HasConstraint -> containsConstraint proxyToField proxyDBU proxySchemaU

            doQuery :: P.Connection -> IO Int64
            doQuery = case everyToField of
                EveryConstraint -> \conn -> P.execute conn statement parameters

            proxyU :: Proxy (PostgresUniverse m)
            proxyU = Proxy

            proxyToField :: Proxy PTF.ToField
            proxyToField = Proxy

            proxyDBFlat :: Proxy (Snds (Concat (Snds db)))
            proxyDBFlat = Proxy

            proxyDBU :: Proxy (Fmap (PostgresUniverse m) (Snds (Concat (Snds db))))
            proxyDBU = Proxy

            proxySchema :: Proxy (Snds schema)
            proxySchema = Proxy

            proxySchemaU :: Proxy (Fmap (PostgresUniverse m) (Snds schema))
            proxySchemaU = Proxy

        in  PostgresT $ do
                conn <- ask
                liftIO (doQuery conn)
                return ()

    type InterpreterUpdateConstraint (PostgresInterpreter m) db =
             ( Every PTF.ToField (Fmap (PostgresUniverse m) (Snds (Concat (Snds db))))
             , Every PTF.ToField (Fmap (PostgresUniverse m) (Snds (Concat (Snds db))))
             )

    interpretUpdate proxyPI (proxyDB :: Proxy db) update@(Update table project (condition :: Condition conditioned) (row :: Row projected)) =
        let statement :: P.Query
            statement = fromString (makeUpdateStatement update)

            conditionParameters :: HList (Fmap (PostgresUniverse m) (Snds (Concat conditioned)))
            conditionParameters = allToUniverse proxyU proxyDB (conditionValues (updateCondition update))

            hlist :: HList (Snds projected)
            hlist = case rowToHListProof (updateColumns update) of
                HasConstraint -> rowToHList (updateColumns update)

            assignmentParameters :: HList (Fmap (PostgresUniverse m) (Snds projected))
            assignmentParameters = allToUniverse proxyU proxyDB hlist

            parameters = assignmentParameters PT.:. conditionParameters

            containsFmapProofCond = fmapContainsProof proxyU proxyDBFlat proxyConditioned
            containsFmapProofPrj = fmapContainsProof proxyU proxyDBFlat proxyProjected

            everyToFieldCond = case containsFmapProofCond of
                HasConstraint -> containsConstraint proxyToField proxyDBU proxyConditionedU

            everyToFieldPrj = case containsFmapProofPrj of
                HasConstraint -> containsConstraint proxyToField proxyDBU proxyProjectedU

            doQuery :: P.Connection -> IO Int64
            doQuery = case (everyToFieldPrj, everyToFieldCond) of
                (EveryConstraint, EveryConstraint) -> \conn ->
                    P.execute conn statement parameters

            proxyU :: Proxy (PostgresUniverse m)
            proxyU = Proxy

            proxyDBFlat :: Proxy (Snds (Concat (Snds db)))
            proxyDBFlat = Proxy

            proxyDBU :: Proxy (Fmap (PostgresUniverse m) (Snds (Concat (Snds db))))
            proxyDBU = Proxy

            proxyToField :: Proxy PTF.ToField
            proxyToField = Proxy

            proxyConditioned :: Proxy (Snds (Concat conditioned))
            proxyConditioned = Proxy

            proxyConditionedU :: Proxy (Fmap (PostgresUniverse m) (Snds (Concat conditioned)))
            proxyConditionedU = Proxy

            proxyProjected :: Proxy (Snds projected)
            proxyProjected = Proxy

            proxyProjectedU :: Proxy (Fmap (PostgresUniverse m) (Snds projected))
            proxyProjectedU = Proxy

        in  PostgresT $ do
                conn <- ask
                liftIO (doQuery conn)
                return ()

    type InterpreterDeleteConstraint (PostgresInterpreter m) db =
             ( Every PTF.ToField (Fmap (PostgresUniverse m) (Snds (Concat (Snds db))))
             ) 

    interpretDelete proxyU (proxyDB :: Proxy db) delete@(Delete table (condition :: Condition conditioned)) =
        let statement :: P.Query
            statement = fromString (makeDeleteStatement delete)

            parameters :: HList (Fmap (PostgresUniverse m) (Snds (Concat conditioned)))
            parameters = allToUniverse proxyU proxyDB (conditionValues (deleteCondition delete))

            containsFmapProof = fmapContainsProof proxyU proxyDBFlat proxyConditioned

            everyToField = case containsFmapProof of
                HasConstraint -> containsConstraint proxyToField proxyDBU proxyConditionedU
 
            doQuery :: P.Connection -> IO Int64
            doQuery = case everyToField of
                EveryConstraint -> \conn -> P.execute conn statement parameters

            proxyU :: Proxy (Universe (PostgresInterpreter m))
            proxyU = Proxy

            proxyToField :: Proxy PTF.ToField
            proxyToField = Proxy

            proxyDBFlat :: Proxy (Snds (Concat (Snds db)))
            proxyDBFlat = Proxy

            proxyDBU :: Proxy (Fmap (PostgresUniverse m) (Snds (Concat (Snds db))))
            proxyDBU = Proxy

            proxyConditioned :: Proxy (Snds (Concat conditioned))
            proxyConditioned = Proxy

            proxyConditionedU :: Proxy (Fmap (PostgresUniverse m) (Snds (Concat conditioned)))
            proxyConditionedU = Proxy

        in  PostgresT $ do
                conn <- ask
                liftIO (doQuery conn)
                return ()

instance Show (Universe (PostgresInterpreter m) t) where
  show u = case u of
      UText t -> show t
      UBytes t -> show t
      UInt i -> show i
      UDouble d -> show d
      UBool b -> show b
      UDay d -> show d
      UUUID u -> show u
      UNullable mebe -> show mebe

instance InUniverse (PostgresUniverse m) T.Text where
  type UniverseType (PostgresUniverse m) T.Text = T.Text
  toUniverse proxy = UText
  fromUniverse proxy (UText t) = Just t
  toUniverseAssociated proxy t = UText t
  fromUniverseAssociated (UText t) = t

instance InUniverse (PostgresUniverse m) BS.ByteString where
  type UniverseType (PostgresUniverse m) BS.ByteString = BS.ByteString
  toUniverse proxy = UBytes
  fromUniverse proxy (UBytes bs) = Just bs
  toUniverseAssociated proxy bs = UBytes bs
  fromUniverseAssociated (UBytes bs) = bs

instance InUniverse (PostgresUniverse m) Int where
  type UniverseType (PostgresUniverse m) Int = Int
  toUniverse proxy = UInt
  fromUniverse proxy (UInt i) = Just i
  toUniverseAssociated proxy i = UInt i
  fromUniverseAssociated (UInt i) = i

instance InUniverse (PostgresUniverse m) Double where
  type UniverseType (PostgresUniverse m) Double = Double
  toUniverse proxy = UDouble
  fromUniverse proxy (UDouble d) = Just d
  toUniverseAssociated proxy d = UDouble d
  fromUniverseAssociated (UDouble d) = d

instance InUniverse (PostgresUniverse m) Bool where
  type UniverseType (PostgresUniverse m) Bool = Bool
  toUniverse proxy = UBool
  fromUniverse proxy (UBool b) = Just b
  toUniverseAssociated proxy b = UBool b
  fromUniverseAssociated (UBool b) = b

instance InUniverse (PostgresUniverse m) Day where
  type UniverseType (PostgresUniverse m) Day = Day
  toUniverse proxy = UDay
  fromUniverse proxy (UDay d) = Just d
  toUniverseAssociated proxy = UDay
  fromUniverseAssociated (UDay d) = d

instance InUniverse (PostgresUniverse m) UUID where
  type UniverseType (PostgresUniverse m) UUID = UUID
  toUniverse proxy = UUUID
  fromUniverse proxy (UUUID u) = Just u
  toUniverseAssociated proxy = UUUID
  fromUniverseAssociated (UUUID u) = u

instance InUniverse (PostgresUniverse m) UTCTime where
  toUniverse proxy = UUTCTime
  fromUniverse proxy (UUTCTime t) = Just t
  type UniverseType (PostgresUniverse m) UTCTime = UTCTime
  toUniverseAssociated proxy = UUTCTime
  fromUniverseAssociated (UUTCTime t) = t

instance InUniverse (PostgresUniverse m) a => InUniverse (PostgresUniverse m) (Maybe a) where
  toUniverse proxyU = UNullable . fmap (toUniverse proxyU)
  fromUniverse (Proxy :: Proxy (Maybe a)) (UNullable x) = do
      contents <- x
      return $ fromUniverse (Proxy :: Proxy a) contents
  type UniverseType (PostgresUniverse m) (Maybe a) = Maybe (UniverseType (PostgresUniverse m) a)
  toUniverseAssociated proxy = UNullable . fmap (toUniverseAssociated proxy)
  fromUniverseAssociated (UNullable x) = fmap fromUniverseAssociated x

instance PTF.ToField T.Text => PTF.ToField ((Universe (PostgresInterpreter m)) t) where
  toField u = case u of
      UText str -> PTF.toField str
      UBytes bs -> PTF.toField (PT.Binary bs)
      UInt i -> PTF.toField i
      UDouble d -> PTF.toField d
      UBool b -> PTF.toField b
      UDay d -> PTF.toField d
      UUTCTime t -> PTF.toField t
      UUUID t -> PTF.toField t
      UNullable mebe -> PTF.toField mebe

instance
       ( InUniverse (Universe (PostgresInterpreter m)) t
       , PFF.FromField (UniverseType (Universe (PostgresInterpreter m)) t)
       )
    => PFF.FromField (Universe (PostgresInterpreter m) t)
  where
    fromField = let otherParser :: PFF.FieldParser (UniverseType (Universe (PostgresInterpreter m)) t)
                    otherParser = PFF.fromField
                in  \field bytestring -> fmap (toUniverseAssociated Proxy) (otherParser field bytestring)


postgresProxy :: Proxy (PostgresInterpreter m)
postgresProxy = Proxy

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

-- After that FromRow instance, the ToRow instance is a big relief.

instance (Every PTF.ToField types) => PTR.ToRow (HList types) where
  toRow lst = case lst of
      EmptyHList -> []
      ConsHList v rest -> PTF.toField v : PTR.toRow rest

makeInsertStatement :: Insert '(sym, schema) -> String
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

    makeInsertColumns :: Schema ss -> [String]
    makeInsertColumns sch = case sch of
        EmptySchema -> []
        ConsSchema col rest -> columnName col : makeInsertColumns rest

    makeSchemaFields :: Schema ss -> [String]
    makeSchemaFields sch = case sch of
        EmptySchema -> []
        ConsSchema _ rest -> "?" : makeSchemaFields rest

makeDeleteStatement :: Delete '(sym, schema) conditioned -> String
makeDeleteStatement delete =
    concat
    [ "DELETE FROM "
    , tableName (deleteTable delete)
    , " WHERE "
    , conditionClause
    ]
  where
    conditionClause = makeConditionClause (deleteCondition delete)

makeUpdateStatement :: Update '(sym, schema) projected conditioned -> String
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

    makeAssignments :: Project ps -> [String]
    makeAssignments prj = case prj of
        EmptyProject -> []
        ConsProject col rest -> (concat [columnName col, " = ?"]) : (makeAssignments rest)

data SomeToRow where
    SomeToRow :: PTR.ToRow r => r -> SomeToRow

relationQueryAndParameters
  :: forall (universe :: * -> *) db projected .
     ( Every (InUniverse universe) (Snds (Concat (Snds db)))
     , Every PTF.ToField (Fmap universe (Snds (Concat (Snds db))))
     )
  => Proxy universe
  -> Relation db projected
  -> (String, SomeToRow)
relationQueryAndParameters proxyU term = case term of

    Intersection left right ->
        let (lquery, lparams) = relationQueryAndParameters proxyU left
            (rquery, rparams) = relationQueryAndParameters proxyU right
        in  case (lparams, rparams) of
                (SomeToRow l, SomeToRow r) ->
                    (concat [lquery, " INTERSECT ", rquery], SomeToRow (l PT.:. r))

    Union left right ->
        let (lquery, lparams) = relationQueryAndParameters proxyU left
            (rquery, rparams) = relationQueryAndParameters proxyU right
        in  case (lparams, rparams) of
                (SomeToRow l, SomeToRow r) ->
                    (concat [lquery, " UNION ", rquery], SomeToRow (l PT.:. r))

    Selection select@(Select table selected projected (condition :: Condition conditioned)) ->

        let query = makeSelectQuery select

            parameters :: HList (Fmap universe (Snds (Concat conditioned)))
            parameters = allToUniverse proxyU proxyDB (conditionValues (condition))

            -- Proof of
            --   Contains (Fmap universe (Snds (Concat (Snds db)))) (Fmap (Snds (Concat conditioned)))
            --
            containsFmapProof = fmapContainsProof proxyU proxyDBFlat proxyConditionedFlat

            -- Proof that we can ToField every one of the conditions.
            everyToField = case containsFmapProof of
                HasConstraint -> containsConstraint proxyToField proxyDBU proxyConditionedU

            proxyDB :: Proxy db
            proxyDB = Proxy

            proxyDBFlat :: Proxy (Snds (Concat (Snds db)))
            proxyDBFlat = Proxy

            proxyConditionedFlat :: Proxy (Snds (Concat conditioned))
            proxyConditionedFlat = Proxy

            proxyDBU :: Proxy (Fmap universe (Snds (Concat (Snds db))))
            proxyDBU = Proxy

            proxyConditionedU :: Proxy (Fmap universe (Snds (Concat conditioned)))
            proxyConditionedU = Proxy

            proxyToField :: Proxy PTF.ToField
            proxyToField = Proxy

        in  case everyToField of
                EveryConstraint -> (query, SomeToRow parameters)

makeSelectQuery
  :: Select '(tableName, schema) selected projected conditioned
  -> String
makeSelectQuery select =
    concat
    [ "SELECT "
    , projectionClause
    , " FROM "
    , tableName (selectTable select)
    , " WHERE "
    , conditionClause
    ]
  where
    projectionClause = makeProjectionClause (selectProjections select)
    conditionClause = makeConditionClause (selectCondition select)

makeProjectionClause :: (Project ss, Project ts) -> String
makeProjectionClause = concat . intersperse "," . makeSelectFields

  where

    makeSelectFields :: (Project ss, Project ts) -> [String]
    makeSelectFields ps = case ps of
        (EmptyProject, EmptyProject) -> []
        (ConsProject col rest, ConsProject col' rest') ->
            (concat [columnName col, " as ", columnName col']) : makeSelectFields (rest, rest')

makeConditionClause :: Condition css -> String
makeConditionClause constr = case constr of
  AndCondition disjunction rest -> concat ["( ", makeDisjunctionClause disjunction, " ) AND ", makeConditionClause rest]
  AlwaysTrue -> "1=1" -- Can we put "True" ? or "true" ?

makeDisjunctionClause :: ConditionDisjunction cs -> String
makeDisjunctionClause disj = case disj of
  OrCondition terminal rest -> concat ["( ", makeTerminalClause terminal, ") OR ", makeDisjunctionClause rest]
  AlwaysFalse -> "1=0" -- Can we put "False" ? or "false" ?

makeTerminalClause :: ConditionTerminal t -> String
makeTerminalClause term = case term of
  -- We use a ? because query parameter substitution shall be done by another
  -- system, namely postgresql-simple.
  EqCondition field -> concat [columnName (fieldColumn field), " = ?"]
  LtCondition field -> concat [columnName (fieldColumn field), " < ?"]
  GtCondition field -> concat [columnName (fieldColumn field), " > ?"]
