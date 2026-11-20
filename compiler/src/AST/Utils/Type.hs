module AST.Utils.Type
  ( delambda
  , dealias
  , deepDealias
  , iteratedDealias
  , aliasBodyToConvert
  )
  where


import qualified Data.Map as Map

import AST.Canonical (Type(..), AliasType(..), FieldType(..))
import qualified AST.Prim.Name as N
import qualified AST.Prim.TypeVar as T



-- DELAMBDA


delambda :: Type -> [Type]
delambda tipe =
  case tipe of
    TLambda arg result ->
      arg : delambda result

    _ ->
      [tipe]



-- DEALIAS


dealias :: [(T.Var, Type)] -> AliasType -> Type
dealias args aliasType =
  case aliasType of
    Holey  tipe -> dealiasHelp (Map.fromList args) tipe
    Filled tipe -> tipe


dealiasHelp :: Map.Map T.Var Type -> Type -> Type
dealiasHelp typeTable =
    go
  where
    go tipe =
      case tipe of
        TLambda a b     -> TLambda (go a) (go b)
        TVar x          -> Map.findWithDefault tipe x typeTable
        TRecord fs e    -> dealiasRecord typeTable (Map.map (dealiasField typeTable) fs) e
        TAlias h n xs t -> TAlias h n (map (fmap go) xs) t
        TType  h n xs   -> TType  h n (map go xs)
        TUnit           -> TUnit
        TPair   a b     -> TPair (go a) (go b)
        TTriple a b c   -> TTriple (go a) (go b) (go c)
        TTagRow ts e    -> TTagRow (Map.map (map go) ts) e


dealiasRecord :: Map.Map T.Var Type -> Map.Map N.Name FieldType -> Maybe T.Var -> Type
dealiasRecord typeTable fields ext =
  case ext >>= \x -> Map.lookup x typeTable of
    Nothing ->
      TRecord fields ext

    Just extType ->
      case iteratedDealias extType of
        TRecord subFields subExt -> TRecord (Map.union subFields fields) subExt
        TVar x                   -> TRecord fields (Just x)
        _                        -> TRecord fields ext


dealiasField :: Map.Map T.Var Type -> FieldType -> FieldType
dealiasField typeTable (FieldType index tipe) =
  FieldType index (dealiasHelp typeTable tipe)



-- DEEP DEALIAS


deepDealias :: Type -> Type
deepDealias tipe =
  case tipe of
    TLambda a b     -> TLambda (deepDealias a) (deepDealias b)
    TVar _          -> tipe
    TRecord fs x    -> TRecord (Map.map deepDealiasField fs) x
    TAlias _ _ xs t -> deepDealias (dealias xs t)
    TType h n xs    -> TType h n (map deepDealias xs)
    TUnit           -> TUnit
    TPair   a b     -> TPair (deepDealias a) (deepDealias b)
    TTriple a b c   -> TTriple (deepDealias a) (deepDealias b) (deepDealias c)

    TTagRow tags ext ->
      TTagRow (Map.map (map deepDealias) tags) ext


deepDealiasField :: FieldType -> FieldType
deepDealiasField (FieldType index tipe) =
  FieldType index (deepDealias tipe)



-- ITERATED DEALIAS


iteratedDealias :: Type -> Type
iteratedDealias tipe =
  case tipe of
    TAlias _ _ xs t -> iteratedDealias (dealias xs t)
    _               -> tipe



-- CLOSED RECORD FIELDS


-- The body the type checker converts for a mention of an alias, given the
-- mention's arguments and the alias body: the closed record the alias stands
-- for, with each field once, when it has no parameters and expands to record
-- extensions ending in a closed record; otherwise the body as written.
--
-- Aliases built from nested extensible records, like
-- `type alias T = A.T (B.T (C.T {}))` where `A.T` itself includes `C.T`,
-- reach the same alias along many paths. Converting the alias as written
-- builds every path's fields separately and only merges them during
-- unification, which for large records costs gigabytes. The flat record is
-- the same type with each field once.
--
-- No argument may be copied, or the type checker converts it once per copy,
-- at every level of a nesting: `Box (Box (… Int))` with
-- `type alias Box a = { value : a }` converts each level's argument again as
-- the alias argument, and in `type alias T2 = Twice T1` with
-- `type alias Twice a = { x : a, y : a }` each level doubles. So only
-- aliases without parameters are flattened, and the expansion substitutes a
-- parameter only into a body that uses it at most once.
--
-- The body as written when two copies of a field have different types, so
-- that such a type behaves exactly as without flattening, and whenever the
-- expansion has a shape the substitution below doesn't resolve exactly.
aliasBodyToConvert :: [(T.Var, Type)] -> AliasType -> AliasType
aliasBodyToConvert args aliasType =
  case flatRecordFields args aliasType of
    Just fields -> Filled (TRecord fields Nothing)
    Nothing     -> aliasType


flatRecordFields :: [(T.Var, Type)] -> AliasType -> Maybe (Map.Map N.Name FieldType)
flatRecordFields args aliasType =
  let
    body =
      case aliasType of
        Holey tipe  -> tipe
        Filled tipe -> tipe
  in
  case (args, body) of
    -- Only a body that applies another alias can have extensions to merge;
    -- any other body is converted as written without expanding it.
    ([], TAlias _ _ _ _) ->
      recordFields =<< substitute Map.empty body

    _ ->
      Nothing


-- Takes an alias application with no free type variables.
aliasRecordFields :: Type -> Maybe (Map.Map N.Name FieldType)
aliasRecordFields tipe =
  case tipe of
    TAlias _ _ args (Holey body) | all (<= 1) (variableUses body) ->
      recordFields =<< substitute (Map.fromList args) body

    TAlias _ _ _ (Holey _) ->
      Nothing

    TAlias _ _ _ (Filled body) ->
      -- A Filled body's variables belong to the enclosing scope, so it is
      -- only usable here when it has none.
      recordFields =<< substitute Map.empty body

    _ ->
      Nothing


-- How often each type variable occurs, as a type or as a record or tag row
-- extension. Nested alias bodies are not entered; the expansion checks each
-- one when it reaches it.
variableUses :: Type -> Map.Map T.Var Int
variableUses tipe =
  let
    one x = Map.singleton x (1 :: Int)
    plus = Map.unionWith (+)
    sumOf = foldr (plus . variableUses) Map.empty
    ext = maybe Map.empty one
  in
  case tipe of
    TLambda a b         -> plus (variableUses a) (variableUses b)
    TVar x              -> one x
    TType _ _ args      -> sumOf args
    TRecord fields x    -> plus (ext x) (sumOf (map (\(FieldType _ t) -> t) (Map.elems fields)))
    TUnit               -> Map.empty
    TPair a b           -> sumOf [a, b]
    TTriple a b c       -> sumOf [a, b, c]
    TAlias _ _ args _   -> sumOf (map snd args)
    TTagRow tags x      -> plus (ext x) (sumOf (concat (Map.elems tags)))


recordFields :: Type -> Maybe (Map.Map N.Name FieldType)
recordFields tipe =
  case tipe of
    TRecord fields Nothing -> Just fields
    TAlias _ _ _ _         -> aliasRecordFields tipe
    _                      -> Nothing


-- Replaces the variables in the table, resolving record extensions bound to
-- closed records into one closed record. Nothing for anything it can't
-- resolve exactly: a variable not in the table, a record extension bound to
-- something other than a closed record, a tag row extension, or a Filled
-- alias body with type variables.
--
-- This is a second alias expansion next to dealiasHelp and dealiasRecord above,
-- on purpose. Those are for showing types and approximate: they drop what
-- they can't resolve, and when an argument repeats a field, its copy wins.
-- The flat record is what the type checker works with, so it has to be
-- exact or not be made at all. Where the type checker meets repeated fields
-- itself (Type.Unify.gatherFields) the outer copy wins; mergeFields only
-- accepts copies that are the same type, so it never has to pick.
substitute :: Map.Map T.Var Type -> Type -> Maybe Type
substitute typeTable tipe =
  let go = substitute typeTable in
  case tipe of
    TLambda a b ->
      TLambda <$> go a <*> go b

    TVar x ->
      Map.lookup x typeTable

    TType home name args ->
      TType home name <$> traverse go args

    TRecord fields Nothing ->
      TRecord <$> traverse (substituteField typeTable) fields <*> pure Nothing

    TRecord fields (Just x) ->
      do  ownFields <- traverse (substituteField typeTable) fields
          extFields <- recordFields =<< Map.lookup x typeTable
          merged <- mergeFields ownFields extFields
          Just (TRecord merged Nothing)

    TUnit ->
      Just TUnit

    TPair a b ->
      TPair <$> go a <*> go b

    TTriple a b c ->
      TTriple <$> go a <*> go b <*> go c

    TAlias home name args aliasType@(Holey _) ->
      TAlias home name <$> traverse (traverse go) args <*> pure aliasType

    -- A Filled body's variables belong to the enclosing scope, not to this
    -- table, so it is kept, unchanged, only when it has none.
    TAlias home name args aliasType@(Filled body) ->
      TAlias home name
        <$> traverse (traverse go) args
        <*> (aliasType <$ substitute Map.empty body)

    TTagRow tags Nothing ->
      TTagRow <$> traverse (traverse go) tags <*> pure Nothing

    TTagRow _ (Just _) ->
      Nothing


substituteField :: Map.Map T.Var Type -> FieldType -> Maybe FieldType
substituteField typeTable (FieldType index tipe) =
  FieldType index <$> substitute typeTable tipe


mergeFields :: Map.Map N.Name FieldType -> Map.Map N.Name FieldType -> Maybe (Map.Map N.Name FieldType)
mergeFields fields1 fields2 =
  sequenceA (Map.unionWith keepIfSame (Map.map Just fields1) (Map.map Just fields2))


-- Field indices are the order of fields in the record they were written in,
-- so copies from different aliases differ there while being the same field.
keepIfSame :: Maybe FieldType -> Maybe FieldType -> Maybe FieldType
keepIfSame maybe1 maybe2 =
  do  field1@(FieldType _ type1) <- maybe1
      FieldType _ type2 <- maybe2
      if type1 == type2 then Just field1 else Nothing
