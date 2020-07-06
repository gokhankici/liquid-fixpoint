{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE OverloadedStrings #-}

-- | This is a wrapper around IO that permits SMT queries

module Language.Fixpoint.Solver.Monad
       ( -- * Type
         SolveM

         -- * Execution
       , runSolverM

         -- * Get Binds
       , getBinds

         -- * SMT Query
       , filterRequired
       , filterValid
       , filterValidGradual
       , checkSat
       , smtEnablembqi

         -- * Debug
       , Stats
       , tickIter
       , stats
       , numIter

       , TraceVarRun(..)
       , TraceVar(..)
       , TraceQualif(..)
       , takeSolverSnapshot
       , writeSolverTrace
       )
       where

import           Control.DeepSeq
import           GHC.Generics
import           Language.Fixpoint.Utils.Progress
import qualified Language.Fixpoint.Types.Config  as C
import           Language.Fixpoint.Types.Config  (Config)
import qualified Language.Fixpoint.Types   as F
-- import qualified Language.Fixpoint.Misc    as Misc
-- import           Language.Fixpoint.SortCheck
import qualified Language.Fixpoint.Types.Solutions as F
import           Language.Fixpoint.Types   (pprint)
-- import qualified Language.Fixpoint.Types.Errors  as E
import           Language.Fixpoint.Smt.Serialize ()
import           Language.Fixpoint.Types.PrettyPrint ()
import           Language.Fixpoint.Smt.Interface
-- import qualified Language.Fixpoint.Smt.Theories as Thy
import           Language.Fixpoint.Solver.Sanitize
import           Language.Fixpoint.Graph.Types (SolverInfo (..))
-- import           Language.Fixpoint.Solver.Solution
-- import           Data.Maybe           (catMaybes)
import           Data.List            (partition)
-- import           Data.Char            (isUpper)
import           Text.PrettyPrint.HughesPJ (text)
import           Control.Monad.State.Strict
import qualified Data.HashMap.Strict as M
import           Data.Maybe (catMaybes)
import           Control.Exception.Base (bracket)
import qualified Data.IntMap as IM
import qualified Data.HashMap.Strict as HM
import           Text.Printf
import           Data.Char
import qualified Data.Aeson as A
import qualified Data.Aeson.Encoding.Internal as AI
import qualified Data.Text as T

--------------------------------------------------------------------------------
-- | Solver Monadic API --------------------------------------------------------
--------------------------------------------------------------------------------

type SolveM = StateT SolverState IO

type SolverTraceElement = M.HashMap F.KVar [TraceQualif]
type SolverTrace = IM.IntMap SolverTraceElement

data SolverState = SS
  { ssCtx     :: !Context          -- ^ SMT Solver Context
  , ssBinds   :: !F.BindEnv        -- ^ All variables and types
  , ssStats   :: !Stats            -- ^ Solver Statistics
  }

data Stats = Stats
  { numCstr :: !Int -- ^ # Horn Constraints
  , numIter :: !Int -- ^ # Refine Iterations
  , numBrkt :: !Int -- ^ # smtBracket    calls (push/pop)
  , numChck :: !Int -- ^ # smtCheckUnsat calls
  , numVald :: !Int -- ^ # times SMT said RHS Valid
  , ssTrace :: !SolverTrace -- ^ Solver Trace
  } deriving (Show, Generic)

instance NFData Stats

stats0    :: F.GInfo c b -> Stats
stats0 fi = Stats nCs 0 0 0 0 mempty
  where
    nCs   = M.size $ F.cm fi


instance F.PTable Stats where
  ptable s = F.DocTable [ (text "# Constraints"         , pprint (numCstr s))
                        , (text "# Refine Iterations"   , pprint (numIter s))
                        , (text "# SMT Brackets"        , pprint (numBrkt s))
                        , (text "# SMT Queries (Valid)" , pprint (numVald s))
                        , (text "# SMT Queries (Total)" , pprint (numChck s))
                        ]

--------------------------------------------------------------------------------
runSolverM :: Config -> SolverInfo b c -> SolveM a -> IO a
--------------------------------------------------------------------------------
runSolverM cfg sI act =
  bracket acquire release $ \ctx -> do
    res <- runStateT act' (s0 ctx)
    smtWrite ctx "(exit)"
    return (fst res)
  where
    s0 ctx   = SS ctx be (stats0 fi)
    act'     = assumesAxioms (F.asserts fi) >> act
    release  = cleanupContext
    acquire  = makeContextWithSEnv cfg file initEnv
    initEnv  = symbolEnv   cfg fi
    be       = F.bs fi
    file     = C.srcFile cfg
    -- only linear arithmentic when: linear flag is on or solver /= Z3
    -- lar     = linear cfg || Z3 /= solver cfg
    fi       = (siQuery sI) {F.hoInfo = F.HOI (C.allowHO cfg) (C.allowHOqs cfg)}


--------------------------------------------------------------------------------
getBinds :: SolveM F.BindEnv
--------------------------------------------------------------------------------
getBinds = ssBinds <$> get

--------------------------------------------------------------------------------
getIter :: SolveM Int
--------------------------------------------------------------------------------
getIter = numIter . ssStats <$> get

--------------------------------------------------------------------------------
incIter, incBrkt :: SolveM ()
--------------------------------------------------------------------------------
incIter   = modifyStats $ \s -> s {numIter = 1 + numIter s}
incBrkt   = modifyStats $ \s -> s {numBrkt = 1 + numBrkt s}

--------------------------------------------------------------------------------
incChck, incVald :: Int -> SolveM ()
--------------------------------------------------------------------------------
incChck n = modifyStats $ \s -> s {numChck = n + numChck s}
incVald n = modifyStats $ \s -> s {numVald = n + numVald s}

withContext :: (Context -> IO a) -> SolveM a
withContext k = (lift . k) =<< getContext

getContext :: SolveM Context
getContext = ssCtx <$> get

modifyStats :: (Stats -> Stats) -> SolveM ()
modifyStats f = modify $ \s -> s { ssStats = f (ssStats s) }

--------------------------------------------------------------------------------
-- | SMT Interface -------------------------------------------------------------
--------------------------------------------------------------------------------
-- | `filterRequired [(x1, p1),...,(xn, pn)] q` returns a minimal list [xi] s.t.
--   /\ [pi] => q
--------------------------------------------------------------------------------
filterRequired :: F.Cand a -> F.Expr -> SolveM [a]
--------------------------------------------------------------------------------
filterRequired = error "TBD:filterRequired"

{-
(set-option :produce-unsat-cores true)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)

; Z3 will only track assertions that are named.

(assert (< 0 x))
(assert (! (< 0 y)       :named b2))
(assert (! (< x 10)      :named b3))
(assert (! (< y 10)      :named b4))
(assert (! (< (+ x y) 0) :named bR))
(check-sat)
(get-unsat-core)

> unsat (b2 bR)
-}

--------------------------------------------------------------------------------
-- | `filterValid p [(x1, q1),...,(xn, qn)]` returns the list `[ xi | p => qi]`
--------------------------------------------------------------------------------
filterValid :: F.SrcSpan -> F.Expr -> F.Cand a -> SolveM [a]
--------------------------------------------------------------------------------
filterValid sp p qs = do
  qs' <- withContext $ \me ->
           smtBracket me "filterValidLHS" $
             filterValid_ sp p qs me
  -- stats
  incBrkt
  incChck (length qs)
  incVald (length qs')
  return qs'

filterValid_ :: F.SrcSpan -> F.Expr -> F.Cand a -> Context -> IO [a]
filterValid_ sp p qs me = catMaybes <$> do
  smtAssert me p
  forM qs $ \(q, x) ->
    smtBracketAt sp me "filterValidRHS" $ do
      smtAssert me (F.PNot q)
      valid <- smtCheckUnsat me
      return $ if valid then Just x else Nothing


--------------------------------------------------------------------------------
-- | `filterValidGradual ps [(x1, q1),...,(xn, qn)]` returns the list `[ xi | p => qi]`
-- | for some p in the list ps
--------------------------------------------------------------------------------
filterValidGradual :: [F.Expr] -> F.Cand a -> SolveM [a]
--------------------------------------------------------------------------------
filterValidGradual p qs = do
  qs' <- withContext $ \me ->
           smtBracket me "filterValidGradualLHS" $
             filterValidGradual_ p qs me
  -- stats
  incBrkt
  incChck (length qs)
  incVald (length qs')
  return qs'

filterValidGradual_ :: [F.Expr] -> F.Cand a -> Context -> IO [a]
filterValidGradual_ ps qs me
  = (map snd . fst) <$> foldM partitionCandidates ([], qs) ps
  where
    partitionCandidates :: (F.Cand a, F.Cand a) -> F.Expr -> IO (F.Cand a, F.Cand a)
    partitionCandidates (ok, candidates) p = do
      (valids', invalids')  <- partition snd <$> filterValidOne_ p candidates me
      let (valids, invalids) = (fst <$> valids', fst <$> invalids')
      return (ok ++ valids, invalids)

filterValidOne_ :: F.Expr -> F.Cand a -> Context -> IO [((F.Expr, a), Bool)]
filterValidOne_ p qs me = do
  smtAssert me p
  forM qs $ \(q, x) ->
    smtBracket me "filterValidRHS" $ do
      smtAssert me (F.PNot q)
      valid <- smtCheckUnsat me
      return $ ((q, x), valid)

smtEnablembqi :: SolveM ()
smtEnablembqi
  = withContext $ \me ->
      smtWrite me "(set-option :smt.mbqi true)"

--------------------------------------------------------------------------------
checkSat :: F.Expr -> SolveM  Bool
--------------------------------------------------------------------------------
checkSat p
  = withContext $ \me ->
      smtBracket me "checkSat" $
        smtCheckSat me p

--------------------------------------------------------------------------------
assumesAxioms :: [F.Triggered F.Expr] -> SolveM ()
--------------------------------------------------------------------------------
assumesAxioms es = withContext $ \me -> forM_  es $ smtAssertAxiom me


---------------------------------------------------------------------------
stats :: SolveM Stats
---------------------------------------------------------------------------
stats = ssStats <$> get

---------------------------------------------------------------------------
tickIter :: Bool -> SolveM Int
---------------------------------------------------------------------------
tickIter newScc = progIter newScc >> incIter >> getIter

progIter :: Bool -> SolveM ()
progIter newScc = lift $ when newScc progressTick

takeSolverSnapshot :: M.HashMap F.KVar F.Expr -> SolveM ()
takeSolverSnapshot te = do
  n <- getIter
  modifyStats $ \s -> s { ssTrace = IM.insert n (go <$> te) (ssTrace s) }
  where
    go (F.PAnd es) = toTracePred . F.simplify <$> es
    go _           = undefined


data TraceVarRun = LeftRun | RightRun deriving (Show, Eq, Generic)
data TraceVar = TraceVar TraceVarRun String Int -- variable name and thread id
              deriving (Show, Eq, Generic)
data TraceQualif = TracePublic TraceVar
                 | TraceUntainted TraceVar
                 | TraceSameTaint TraceVar TraceVar
                 deriving (Show, Eq, Generic)

instance NFData TraceVarRun
instance NFData TraceVar
instance NFData TraceQualif

instance A.ToJSON TraceVarRun
instance A.ToJSON TraceVar
instance A.ToJSON TraceQualif

instance A.ToJSON F.KVar where
  toJSON = A.String . T.pack . F.symbolSafeString . F.kv

instance A.ToJSONKey F.KVar where
  toJSONKey =
    A.ToJSONKeyText (T.pack . toS) (AI.string . toS)
      where toS = F.symbolSafeString . F.kv

toTracePred :: F.Expr -> TraceQualif
toTracePred e@(F.PAtom F.Eq (F.EVar s1) (F.EVar s2))
  | isTaint s1 || isTaint s2 = error $ toTracePredErrorMsg e
  | otherwise =
    let TraceVar r1 v1 n1 = parseTraceVar s1
        TraceVar r2 v2 n2 = parseTraceVar s2
     in if r1 /= r2 && v1 == v2 && n1 == n2
        then TracePublic (TraceVar LeftRun v1 n1)
        else error $ toTracePredErrorMsg e

toTracePred e@(F.PIff (F.EVar s1) e2) =
  case e2 of
    F.POr [] ->
      TraceUntainted $ parseTraceVar s1
    F.EVar s2 | isTaint s1 && isTaint s2 ->
      TraceSameTaint (parseTraceVar s1) (parseTraceVar s2)
    _ -> error $ toTracePredErrorMsg e

toTracePred e = error $ toTracePredErrorMsg e

toTracePredErrorMsg :: F.Expr -> String
toTracePredErrorMsg e =
  printf "Unexpected expr in toTracePred: %s" (F.showFix $ F.simplify e)

isTaint :: F.Symbol -> Bool
isTaint sym =
  case str of
    'T':_ -> True
    'V':_ -> False
    _     -> error $ printf "Unexpected symbol in isTaint: %s" str
  where
    str = F.symbolSafeString sym


parseTraceVar :: F.Symbol -> TraceVar
parseTraceVar sym =
  TraceVar
  (getVarRun s)
  (reverse $ drop 2 rest)
  (read $ reverse tRev)
  where
    s = F.symbolSafeString sym
    s1 = drop 3 s -- drop the type & run characters
    s1r = reverse s1 -- reverse it to parse the thread id
    (tRev, rest) = span isDigit s1r

    getVarRun (_:'L':'_':_) = LeftRun
    getVarRun (_:'R':'_':_) = RightRun
    getVarRun s = error $ printf "Unexpected symbol in getVarRun: %s" s

writeSolverTrace :: FilePath -> Stats -> IO ()
writeSolverTrace fp stat = do
  A.encodeFile fp (ssTrace stat)
  printSolverTrace stat

printSolverTrace :: Stats -> IO ()
printSolverTrace stat = do
  flip mapM_ (IM.toList $ ssTrace stat) $ \(n, te) -> do
    printf "%d:\n" n
    flip mapM_ (HM.toList te) $ \(kv, ps) -> do
      case ps of
        [] -> return ()
        es -> print kv >> mapM_ print es
    printf "\n\n\n"
