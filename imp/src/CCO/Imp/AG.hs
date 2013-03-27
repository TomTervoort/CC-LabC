

-- UUAGC 0.9.42.2 (AG.ag)
module CCO.Imp.AG where

{-# LINE 2 ".\\AG/CodeGeneration.ag" #-}

import CCO.Ssm hiding (Add, Sub, Mul, Div, Eq, Lt, Gt)
import Prelude hiding (div)

import Data.Maybe
import Control.Arrow
import Data.List
import Data.Ord

import Debug.Trace
{-# LINE 18 "AG.hs" #-}
{-# LINE 5 ".\\AG/Base.ag" #-}

type Ident = String    -- ^ Type of identifiers.
{-# LINE 22 "AG.hs" #-}

{-# LINE 54 ".\\AG/CodeGeneration.ag" #-}

-- | An environment maps identifiers to symbol descriptors.
type Env = [(Ident, Sym)]

-- | A symbol descriptor either describes a variable or a function symbol.
-- For a variable, we store its offset relative to the mark pointer; for
-- a function we store its begin label.
data Sym = V Int | F Int Stmts

-- | Restrict environments to a particular type of descriptor.
vars   env = [entry | entry@(_, V _     ) <- env            ]
funs   env = [entry | entry@(_, F _ _   ) <- env            ]
params env = [entry | entry@(_, V offset) <- env, offset < 0]
{-# LINE 38 "AG.hs" #-}

{-# LINE 89 ".\\AG/CodeGeneration.ag" #-}

-- | A symbol table contains descriptors for each variable that is in scope at
-- a certain program point.
-- The table consists of levels of 'Env's reflecting the nesting of functions:
-- * The head of the list of 'Env's corresponds to the innermost function scope
--   and so it contains the descriptors of the symbols that are allocated
--   relative to the current mark pointer.
-- * To access the symbols described in the tail of the list, static links are
--   to be followed.
type Syms = [Env]
{-# LINE 51 "AG.hs" #-}

{-# LINE 205 ".\\AG/CodeGeneration.ag" #-}

-- | Reversed function application operator. Useful in combination with arrow notation: this can
--   be used to 'feed' an argument to multiple functions combined with >>>.
(<<$) :: a -> (a -> b) -> b
(<<$) x f = f x
infixr 0 <<$

-- | Folds function composition over a list. Useful foir sequencing CodeS.
composeList :: [a -> a] -> a -> a
composeList = foldr (.) id

-- | Produces code for annotating parameters.
enterparams :: Env -> CodeS
enterparams env = composeList [annote MP off off "green" (x ++ " (param)") | (x, V off) <- env]

-- | Produces code for entering a block.
enter :: Env -> CodeS
enter env = composeList [ldc 0 . annote SP 0 0 "green" (x ++ " (var)") | (x, V _) <- env]

-- | Produces code for exiting a block.
exit :: Env -> CodeS
exit env = ajs (- length (vars env))

-- | If a variable is to be retrieved through a static link, this will produce code retrieving the
--   link address, along with the number of scopes that had to be walked in order to find the SL.
getLink :: Ident -> Syms -> Maybe (CodeS, Int)
getLink x (local : global) = case lookup x (vars local) of
                              Nothing -> Just $ first (ldl (-2) .) $ getLink' global
                              Just _  -> Nothing
 where getLink' (env : envs) = case lookup x (vars env) of
                                Nothing -> let (c, i) = getLink' envs
                                            in (lda (-2) . c, i + 1)
                                Just _  -> (id, 0)

-- | Produces code for retrieving the value of a variable.
get :: Ident -> Syms -> CodeS
get x (local : global) = case lookup x (vars local) of
  Nothing         -> getCached x (local:global) -- ldl (- 2) . getGlobal x global
  Just (V offset) -> ldl offset

-- | Produces code for retrieving the value of a global variable.
getGlobal :: Ident -> Syms -> CodeS
getGlobal x []           = error ("unknown variable: " ++ x)
getGlobal x (env : envs) = case lookup x (vars env) of
  Nothing         -> lda (- 2) . getGlobal x envs
  Just (V offset) -> lda offset

-- | Generalizes over getCached and setCached. Provide code that either loads or stores a variable
--   at a given offset from the address on the stack.
withCached :: (Int -> CodeS) -> Ident -> Syms -> CodeS 
withCached op x envs = case getLink x envs of
                        Nothing           -> error ("unknown variable: " ++ x)
                        Just (getLink, _) -> getLink . op offset 
 where offset = case lookup x $ concatMap vars envs of
                 Just (V off) -> off
                 _            -> error ("unknown variable: " ++ x)

-- | Fetches the value of a global variable through the static-link cache. 
getCached :: Ident -> Syms -> CodeS
getCached = withCached lda

-- | Sets a global variable value through the static-link cache. 
setCached :: Ident -> Syms -> CodeS
setCached = withCached sta

-- | Produces code for assigning a new value to a variable.
set :: Ident -> Syms -> CodeS
set x (local : global) = case lookup x (vars local) of
  Nothing         -> setCached x (local:global) -- ldl (- 2) . setGlobal x global
  Just (V offset) -> stl offset

-- | Produces code for assigning a new value to a global variable.
setGlobal :: Ident -> Syms -> CodeS
setGlobal x []           = error ("unknown variable: " ++ x)
setGlobal x (env : envs) = case lookup x (vars env) of
  Nothing         -> lda (- 2) . setGlobal x envs
  Just (V offset) -> sta offset

-- | Produces code for calling a function.
call :: Ident -> Syms -> CodeS
call f (local : global) = case lookup f (funs local) of
  Nothing             -> ldl (- 2) . callGlobal f global
  Just (F beginLabel _) -> ldr MP . ldcL beginLabel . jsr 
                          

-- | Produces code for calling a global function.
callGlobal :: Ident -> Syms -> CodeS
callGlobal f []           = error ("unknown function: " ++ f)
callGlobal f (env : envs) = case lookup f (funs env) of
  Nothing             -> lda (- 2) . callGlobal f envs
  Just (F beginLabel _) -> ldcL beginLabel . jsr

-- | Produces code for returning from a function.
return_ :: Syms -> CodeS
return_ (local : global) =
  sts (- (length (vars local) + 3)) .
  ldrr SP MP .
  str MP .
  sts (- length (params local)) .
  ajs (- (length (params local) - 1)) .
  ret

-- | Preprends a SL cache loader and appends an unloader around some instructions.
wrapSLCacheLoader :: Syms -> CodeS -> CodeS
wrapSLCacheLoader env code = loadSLCache env
                               <<$ first (. code) 
                               >>> second unloadSLCache 
                               >>> uncurry (.)
  
-- | Provides code for loading the static links that are neccessary for allowing fast access to all 
--   relevant variables. Also returns the size of the static link cache.
loadSLCache :: Syms -> (CodeS, Int)
loadSLCache (local : global) | null getters = (id, 0)
                             | otherwise = (composeList getters
                                            . annote SP (-(length getters) + 1) 0 "red" "SLCache"
                                            , length getters)
 where getters :: [CodeS]
       getters = [getLink ident (local:global) | ident <- cacheVars local global] 
                  <<$ catMaybes 
                  >>> sortBy (comparing snd) 
                  >>> nubBy (\(_,i1) (_,i2) -> i1 == i2)
                  >>> map fst

-- | Given a static link cache size. Pop its contents, which should end one above the current SP. 
--   Afterwards, the value the SP pointed to is restored.
unloadSLCache :: Int -> CodeS
unloadSLCache size = ajs (-1 - size)
                      . lds (size + 1)

cacheVars :: Env -> Syms -> [Ident]
cacheVars local global = concatMap (map (filter isRequired . fst) . vars) global
 where --isRequired :: Ident -> Bool
       isRequired ident = True-- stmtsUsesIdent ident (getFunStmtsFromLocal local)
       declUsesIdent :: Ident -> Decl -> Bool
       declUsesIdent i f@(FunDecl name xs stmts _) = stmtsUsesIdent i stmts
       declUsesIdent i _ = False
       stmtsUsesIdent :: Ident -> [Stmt] -> Bool
       stmtsUsesIdent i l = any (stmtUsesIdent i) l
       stmtUsesIdent :: Ident -> Stmt -> Bool
       stmtUsesIdent i (Assign x expr) = exprUsesIdent i expr
       stmtUsesIdent i (Call_ f exprs) = exprsUsesIdent i exprs
       stmtUsesIdent i (Print expr) = exprUsesIdent i expr
       stmtUsesIdent i (Return expr) = exprUsesIdent i expr
       stmtUsesIdent i (If expr s1 s2) = (exprUsesIdent i expr) || (stmtUsesIdent i s1) || (stmtUsesIdent i s2)
       stmtUsesIdent i (Block stmts) = stmtsUsesIdent i stmts 
       stmtUsesIdent i _ = False
       exprsUsesIdent :: Ident -> [Exp] -> Bool
       exprsUsesIdent i l = any (exprUsesIdent i) l
       exprUsesIdent :: Ident -> Exp -> Bool
       exprUsesIdent i (Var i2) = i == i2 
       exprUsesIdent i (Call f exps) = exprsUsesIdent i exps
       exprUsesIdent i (Add e1 e2) = (exprUsesIdent i e1) || (exprUsesIdent i e2)
       exprUsesIdent i (Sub e1 e2) = (exprUsesIdent i e1) || (exprUsesIdent i e2)
       exprUsesIdent i (Mul e1 e2) = (exprUsesIdent i e1) || (exprUsesIdent i e2)
       exprUsesIdent i (Div e1 e2) = (exprUsesIdent i e1) || (exprUsesIdent i e2)
       exprUsesIdent i (Lt e1 e2) = (exprUsesIdent i e1) || (exprUsesIdent i e2)
       exprUsesIdent i (Eq e1 e2) = (exprUsesIdent i e1) || (exprUsesIdent i e2)
       exprUsesIdent i (Gt e1 e2) = (exprUsesIdent i e1) || (exprUsesIdent i e2)
       exprUsesIdent i _ = False

--getFunStmtsFromLocal :: Env -> [Stmt]
getFunStmtsFromLocal = [] -- TODO
{-# LINE 216 "AG.hs" #-}
-- Decl --------------------------------------------------------
data Decl = VarDecl (Ident)
          | FunDecl (Ident) (([Ident])) (Stmts) (( Stmts ))
-- cata
sem_Decl :: Decl ->
            T_Decl
sem_Decl (VarDecl _x) =
    (sem_Decl_VarDecl _x)
sem_Decl (FunDecl _f _xs _b _c) =
    (sem_Decl_FunDecl _f _xs (sem_Stmts _b) _c)
-- semantic domain
type T_Decl = ([Label]) ->
              Int ->
              Syms ->
              ( CodeS,Env,([Label]),Int)
data Inh_Decl = Inh_Decl {labels_Inh_Decl :: ([Label]),offset_Inh_Decl :: Int,syms_Inh_Decl :: Syms}
data Syn_Decl = Syn_Decl {codes_Syn_Decl :: CodeS,env_Syn_Decl :: Env,labels_Syn_Decl :: ([Label]),offset_Syn_Decl :: Int}
wrap_Decl :: T_Decl ->
             Inh_Decl ->
             Syn_Decl
wrap_Decl sem (Inh_Decl _lhsIlabels _lhsIoffset _lhsIsyms) =
    (let ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset) = sem _lhsIlabels _lhsIoffset _lhsIsyms
     in  (Syn_Decl _lhsOcodes _lhsOenv _lhsOlabels _lhsOoffset))
sem_Decl_VarDecl :: Ident ->
                    T_Decl
sem_Decl_VarDecl x_ =
    (\ _lhsIlabels
       _lhsIoffset
       _lhsIsyms ->
         (let _lhsOoffset :: Int
              _lhsOenv :: Env
              _lhsOcodes :: CodeS
              _lhsOlabels :: ([Label])
              _lhsOoffset =
                  ({-# LINE 46 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIoffset + 1
                   {-# LINE 253 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 75 ".\\AG/CodeGeneration.ag" #-}
                   [(x_, V _lhsIoffset    )]
                   {-# LINE 258 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 143 ".\\AG/CodeGeneration.ag" #-}
                   id
                   {-# LINE 263 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 268 "AG.hs" #-}
                   )
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset)))
sem_Decl_FunDecl :: Ident ->
                    ([Ident]) ->
                    T_Stmts ->
                    ( Stmts ) ->
                    T_Decl
sem_Decl_FunDecl f_ xs_ b_ c_ =
    (\ _lhsIlabels
       _lhsIoffset
       _lhsIsyms ->
         (let _bOlabels :: ([Label])
              _bOoffset :: Int
              _lhsOenv :: Env
              _bOsyms :: Syms
              _lhsOcodes :: CodeS
              _lhsOlabels :: ([Label])
              _lhsOoffset :: Int
              _bIcodes :: CodeS
              _bIenv :: Env
              _bIlabels :: ([Label])
              _bIoffset :: Int
              _beginLabel =
                  ({-# LINE 26 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIlabels !! 0
                   {-# LINE 294 "AG.hs" #-}
                   )
              _endLabel =
                  ({-# LINE 27 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIlabels !! 1
                   {-# LINE 299 "AG.hs" #-}
                   )
              _bOlabels =
                  ({-# LINE 28 ".\\AG/CodeGeneration.ag" #-}
                   drop 2 _lhsIlabels
                   {-# LINE 304 "AG.hs" #-}
                   )
              _bOoffset =
                  ({-# LINE 47 ".\\AG/CodeGeneration.ag" #-}
                   1
                   {-# LINE 309 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 76 ".\\AG/CodeGeneration.ag" #-}
                   [(f_, (F _beginLabel     c_))]
                   {-# LINE 314 "AG.hs" #-}
                   )
              _params =
                  ({-# LINE 83 ".\\AG/CodeGeneration.ag" #-}
                   zipWith (\x i -> (x, V i)) xs_ [- (2 + length xs_) ..]
                   {-# LINE 319 "AG.hs" #-}
                   )
              _bOsyms =
                  ({-# LINE 107 ".\\AG/CodeGeneration.ag" #-}
                   (_params     ++ _bIenv) : _lhsIsyms
                   {-# LINE 324 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 151 ".\\AG/CodeGeneration.ag" #-}
                   bra _endLabel     .
                   label _beginLabel     .
                     ldr MP .
                     ldrr MP SP .
                     enterparams _params     .
                     enter _bIenv .
                     _bIcodes .
                     exit _bIenv .
                     ldc 0 .
                     return_ (_params     : _lhsIsyms) .
                   label _endLabel
                   {-# LINE 339 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 ".\\AG/CodeGeneration.ag" #-}
                   _bIlabels
                   {-# LINE 344 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 43 ".\\AG/CodeGeneration.ag" #-}
                   _bIoffset
                   {-# LINE 349 "AG.hs" #-}
                   )
              ( _bIcodes,_bIenv,_bIlabels,_bIoffset) =
                  b_ _bOlabels _bOoffset _bOsyms
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset)))
-- Decls -------------------------------------------------------
type Decls = [Decl]
-- cata
sem_Decls :: Decls ->
             T_Decls
sem_Decls list =
    (Prelude.foldr sem_Decls_Cons sem_Decls_Nil (Prelude.map sem_Decl list))
-- semantic domain
type T_Decls = ([Label]) ->
               Int ->
               Syms ->
               ( CodeS,Env,([Label]),Int)
data Inh_Decls = Inh_Decls {labels_Inh_Decls :: ([Label]),offset_Inh_Decls :: Int,syms_Inh_Decls :: Syms}
data Syn_Decls = Syn_Decls {codes_Syn_Decls :: CodeS,env_Syn_Decls :: Env,labels_Syn_Decls :: ([Label]),offset_Syn_Decls :: Int}
wrap_Decls :: T_Decls ->
              Inh_Decls ->
              Syn_Decls
wrap_Decls sem (Inh_Decls _lhsIlabels _lhsIoffset _lhsIsyms) =
    (let ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset) = sem _lhsIlabels _lhsIoffset _lhsIsyms
     in  (Syn_Decls _lhsOcodes _lhsOenv _lhsOlabels _lhsOoffset))
sem_Decls_Cons :: T_Decl ->
                  T_Decls ->
                  T_Decls
sem_Decls_Cons hd_ tl_ =
    (\ _lhsIlabels
       _lhsIoffset
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOenv :: Env
              _lhsOlabels :: ([Label])
              _lhsOoffset :: Int
              _hdOlabels :: ([Label])
              _hdOoffset :: Int
              _hdOsyms :: Syms
              _tlOlabels :: ([Label])
              _tlOoffset :: Int
              _tlOsyms :: Syms
              _hdIcodes :: CodeS
              _hdIenv :: Env
              _hdIlabels :: ([Label])
              _hdIoffset :: Int
              _tlIcodes :: CodeS
              _tlIenv :: Env
              _tlIlabels :: ([Label])
              _tlIoffset :: Int
              _lhsOcodes =
                  ({-# LINE 143 ".\\AG/CodeGeneration.ag" #-}
                   _hdIcodes . _tlIcodes
                   {-# LINE 402 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 73 ".\\AG/CodeGeneration.ag" #-}
                   _hdIenv ++ _tlIenv
                   {-# LINE 407 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 ".\\AG/CodeGeneration.ag" #-}
                   _tlIlabels
                   {-# LINE 412 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 43 ".\\AG/CodeGeneration.ag" #-}
                   _tlIoffset
                   {-# LINE 417 "AG.hs" #-}
                   )
              _hdOlabels =
                  ({-# LINE 21 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 422 "AG.hs" #-}
                   )
              _hdOoffset =
                  ({-# LINE 42 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 427 "AG.hs" #-}
                   )
              _hdOsyms =
                  ({-# LINE 104 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 432 "AG.hs" #-}
                   )
              _tlOlabels =
                  ({-# LINE 21 ".\\AG/CodeGeneration.ag" #-}
                   _hdIlabels
                   {-# LINE 437 "AG.hs" #-}
                   )
              _tlOoffset =
                  ({-# LINE 42 ".\\AG/CodeGeneration.ag" #-}
                   _hdIoffset
                   {-# LINE 442 "AG.hs" #-}
                   )
              _tlOsyms =
                  ({-# LINE 104 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 447 "AG.hs" #-}
                   )
              ( _hdIcodes,_hdIenv,_hdIlabels,_hdIoffset) =
                  hd_ _hdOlabels _hdOoffset _hdOsyms
              ( _tlIcodes,_tlIenv,_tlIlabels,_tlIoffset) =
                  tl_ _tlOlabels _tlOoffset _tlOsyms
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset)))
sem_Decls_Nil :: T_Decls
sem_Decls_Nil =
    (\ _lhsIlabels
       _lhsIoffset
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOenv :: Env
              _lhsOlabels :: ([Label])
              _lhsOoffset :: Int
              _lhsOcodes =
                  ({-# LINE 143 ".\\AG/CodeGeneration.ag" #-}
                   id
                   {-# LINE 466 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 73 ".\\AG/CodeGeneration.ag" #-}
                   []
                   {-# LINE 471 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 476 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 43 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 481 "AG.hs" #-}
                   )
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset)))
-- Exp ---------------------------------------------------------
data Exp = Int (Int)
         | False_
         | True_
         | Var (Ident)
         | Call (Ident) (Exps)
         | Add (Exp) (Exp)
         | Sub (Exp) (Exp)
         | Mul (Exp) (Exp)
         | Div (Exp) (Exp)
         | Lt (Exp) (Exp)
         | Eq (Exp) (Exp)
         | Gt (Exp) (Exp)
-- cata
sem_Exp :: Exp ->
           T_Exp
sem_Exp (Int _n) =
    (sem_Exp_Int _n)
sem_Exp (False_) =
    (sem_Exp_False_)
sem_Exp (True_) =
    (sem_Exp_True_)
sem_Exp (Var _x) =
    (sem_Exp_Var _x)
sem_Exp (Call _f _es) =
    (sem_Exp_Call _f (sem_Exps _es))
sem_Exp (Add _e1 _e2) =
    (sem_Exp_Add (sem_Exp _e1) (sem_Exp _e2))
sem_Exp (Sub _e1 _e2) =
    (sem_Exp_Sub (sem_Exp _e1) (sem_Exp _e2))
sem_Exp (Mul _e1 _e2) =
    (sem_Exp_Mul (sem_Exp _e1) (sem_Exp _e2))
sem_Exp (Div _e1 _e2) =
    (sem_Exp_Div (sem_Exp _e1) (sem_Exp _e2))
sem_Exp (Lt _e1 _e2) =
    (sem_Exp_Lt (sem_Exp _e1) (sem_Exp _e2))
sem_Exp (Eq _e1 _e2) =
    (sem_Exp_Eq (sem_Exp _e1) (sem_Exp _e2))
sem_Exp (Gt _e1 _e2) =
    (sem_Exp_Gt (sem_Exp _e1) (sem_Exp _e2))
-- semantic domain
type T_Exp = ([Label]) ->
             Syms ->
             ( String,CodeS,([Label]))
data Inh_Exp = Inh_Exp {labels_Inh_Exp :: ([Label]),syms_Inh_Exp :: Syms}
data Syn_Exp = Syn_Exp {ann_Syn_Exp :: String,codes_Syn_Exp :: CodeS,labels_Syn_Exp :: ([Label])}
wrap_Exp :: T_Exp ->
            Inh_Exp ->
            Syn_Exp
wrap_Exp sem (Inh_Exp _lhsIlabels _lhsIsyms) =
    (let ( _lhsOann,_lhsOcodes,_lhsOlabels) = sem _lhsIlabels _lhsIsyms
     in  (Syn_Exp _lhsOann _lhsOcodes _lhsOlabels))
sem_Exp_Int :: Int ->
               T_Exp
sem_Exp_Int n_ =
    (\ _lhsIlabels
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOann :: String
              _lhsOlabels :: ([Label])
              _ann =
                  ({-# LINE 120 ".\\AG/CodeGeneration.ag" #-}
                   show n_
                   {-# LINE 547 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 136 ".\\AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 552 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 181 ".\\AG/CodeGeneration.ag" #-}
                   ldc n_ . _annote
                   {-# LINE 557 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 116 ".\\AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 562 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 567 "AG.hs" #-}
                   )
          in  ( _lhsOann,_lhsOcodes,_lhsOlabels)))
sem_Exp_False_ :: T_Exp
sem_Exp_False_ =
    (\ _lhsIlabels
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOann :: String
              _lhsOlabels :: ([Label])
              _ann =
                  ({-# LINE 121 ".\\AG/CodeGeneration.ag" #-}
                   "False"
                   {-# LINE 580 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 136 ".\\AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 585 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 182 ".\\AG/CodeGeneration.ag" #-}
                   ldc 0 . _annote
                   {-# LINE 590 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 116 ".\\AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 595 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 600 "AG.hs" #-}
                   )
          in  ( _lhsOann,_lhsOcodes,_lhsOlabels)))
sem_Exp_True_ :: T_Exp
sem_Exp_True_ =
    (\ _lhsIlabels
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOann :: String
              _lhsOlabels :: ([Label])
              _ann =
                  ({-# LINE 122 ".\\AG/CodeGeneration.ag" #-}
                   "True"
                   {-# LINE 613 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 136 ".\\AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 618 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 183 ".\\AG/CodeGeneration.ag" #-}
                   ldc 1 . _annote
                   {-# LINE 623 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 116 ".\\AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 628 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 633 "AG.hs" #-}
                   )
          in  ( _lhsOann,_lhsOcodes,_lhsOlabels)))
sem_Exp_Var :: Ident ->
               T_Exp
sem_Exp_Var x_ =
    (\ _lhsIlabels
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOann :: String
              _lhsOlabels :: ([Label])
              _ann =
                  ({-# LINE 123 ".\\AG/CodeGeneration.ag" #-}
                   x_
                   {-# LINE 647 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 136 ".\\AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 652 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 184 ".\\AG/CodeGeneration.ag" #-}
                   get x_ _lhsIsyms . _annote
                   {-# LINE 657 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 116 ".\\AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 662 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 667 "AG.hs" #-}
                   )
          in  ( _lhsOann,_lhsOcodes,_lhsOlabels)))
sem_Exp_Call :: Ident ->
                T_Exps ->
                T_Exp
sem_Exp_Call f_ es_ =
    (\ _lhsIlabels
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOann :: String
              _lhsOlabels :: ([Label])
              _esOlabels :: ([Label])
              _esOsyms :: Syms
              _esIanns :: ([String])
              _esIcodes :: CodeS
              _esIlabels :: ([Label])
              _ann =
                  ({-# LINE 124 ".\\AG/CodeGeneration.ag" #-}
                   f_ ++ "(" ++ concat (intersperse "," _esIanns) ++ ")"
                   {-# LINE 687 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 136 ".\\AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 692 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 185 ".\\AG/CodeGeneration.ag" #-}
                   wrapSLCacheLoader _lhsIsyms
                    (_esIcodes .
                     call f_ _lhsIsyms)
                   {-# LINE 699 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 116 ".\\AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 704 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 ".\\AG/CodeGeneration.ag" #-}
                   _esIlabels
                   {-# LINE 709 "AG.hs" #-}
                   )
              _esOlabels =
                  ({-# LINE 21 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 714 "AG.hs" #-}
                   )
              _esOsyms =
                  ({-# LINE 104 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 719 "AG.hs" #-}
                   )
              ( _esIanns,_esIcodes,_esIlabels) =
                  es_ _esOlabels _esOsyms
          in  ( _lhsOann,_lhsOcodes,_lhsOlabels)))
sem_Exp_Add :: T_Exp ->
               T_Exp ->
               T_Exp
sem_Exp_Add e1_ e2_ =
    (\ _lhsIlabels
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOann :: String
              _lhsOlabels :: ([Label])
              _e1Olabels :: ([Label])
              _e1Osyms :: Syms
              _e2Olabels :: ([Label])
              _e2Osyms :: Syms
              _e1Iann :: String
              _e1Icodes :: CodeS
              _e1Ilabels :: ([Label])
              _e2Iann :: String
              _e2Icodes :: CodeS
              _e2Ilabels :: ([Label])
              _ann =
                  ({-# LINE 125 ".\\AG/CodeGeneration.ag" #-}
                   _e1Iann ++ "+"  ++ _e2Iann
                   {-# LINE 746 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 136 ".\\AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 751 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 188 ".\\AG/CodeGeneration.ag" #-}
                   _e1Icodes . _e2Icodes . add . _annote
                   {-# LINE 756 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 116 ".\\AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 761 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 ".\\AG/CodeGeneration.ag" #-}
                   _e2Ilabels
                   {-# LINE 766 "AG.hs" #-}
                   )
              _e1Olabels =
                  ({-# LINE 21 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 771 "AG.hs" #-}
                   )
              _e1Osyms =
                  ({-# LINE 104 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 776 "AG.hs" #-}
                   )
              _e2Olabels =
                  ({-# LINE 21 ".\\AG/CodeGeneration.ag" #-}
                   _e1Ilabels
                   {-# LINE 781 "AG.hs" #-}
                   )
              _e2Osyms =
                  ({-# LINE 104 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 786 "AG.hs" #-}
                   )
              ( _e1Iann,_e1Icodes,_e1Ilabels) =
                  e1_ _e1Olabels _e1Osyms
              ( _e2Iann,_e2Icodes,_e2Ilabels) =
                  e2_ _e2Olabels _e2Osyms
          in  ( _lhsOann,_lhsOcodes,_lhsOlabels)))
sem_Exp_Sub :: T_Exp ->
               T_Exp ->
               T_Exp
sem_Exp_Sub e1_ e2_ =
    (\ _lhsIlabels
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOann :: String
              _lhsOlabels :: ([Label])
              _e1Olabels :: ([Label])
              _e1Osyms :: Syms
              _e2Olabels :: ([Label])
              _e2Osyms :: Syms
              _e1Iann :: String
              _e1Icodes :: CodeS
              _e1Ilabels :: ([Label])
              _e2Iann :: String
              _e2Icodes :: CodeS
              _e2Ilabels :: ([Label])
              _ann =
                  ({-# LINE 126 ".\\AG/CodeGeneration.ag" #-}
                   _e1Iann ++ "-"  ++ _e2Iann
                   {-# LINE 815 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 136 ".\\AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 820 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 189 ".\\AG/CodeGeneration.ag" #-}
                   _e1Icodes . _e2Icodes . sub . _annote
                   {-# LINE 825 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 116 ".\\AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 830 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 ".\\AG/CodeGeneration.ag" #-}
                   _e2Ilabels
                   {-# LINE 835 "AG.hs" #-}
                   )
              _e1Olabels =
                  ({-# LINE 21 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 840 "AG.hs" #-}
                   )
              _e1Osyms =
                  ({-# LINE 104 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 845 "AG.hs" #-}
                   )
              _e2Olabels =
                  ({-# LINE 21 ".\\AG/CodeGeneration.ag" #-}
                   _e1Ilabels
                   {-# LINE 850 "AG.hs" #-}
                   )
              _e2Osyms =
                  ({-# LINE 104 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 855 "AG.hs" #-}
                   )
              ( _e1Iann,_e1Icodes,_e1Ilabels) =
                  e1_ _e1Olabels _e1Osyms
              ( _e2Iann,_e2Icodes,_e2Ilabels) =
                  e2_ _e2Olabels _e2Osyms
          in  ( _lhsOann,_lhsOcodes,_lhsOlabels)))
sem_Exp_Mul :: T_Exp ->
               T_Exp ->
               T_Exp
sem_Exp_Mul e1_ e2_ =
    (\ _lhsIlabels
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOann :: String
              _lhsOlabels :: ([Label])
              _e1Olabels :: ([Label])
              _e1Osyms :: Syms
              _e2Olabels :: ([Label])
              _e2Osyms :: Syms
              _e1Iann :: String
              _e1Icodes :: CodeS
              _e1Ilabels :: ([Label])
              _e2Iann :: String
              _e2Icodes :: CodeS
              _e2Ilabels :: ([Label])
              _ann =
                  ({-# LINE 127 ".\\AG/CodeGeneration.ag" #-}
                   _e1Iann ++ "*"  ++ _e2Iann
                   {-# LINE 884 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 136 ".\\AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 889 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 190 ".\\AG/CodeGeneration.ag" #-}
                   _e1Icodes . _e2Icodes . mul . _annote
                   {-# LINE 894 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 116 ".\\AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 899 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 ".\\AG/CodeGeneration.ag" #-}
                   _e2Ilabels
                   {-# LINE 904 "AG.hs" #-}
                   )
              _e1Olabels =
                  ({-# LINE 21 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 909 "AG.hs" #-}
                   )
              _e1Osyms =
                  ({-# LINE 104 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 914 "AG.hs" #-}
                   )
              _e2Olabels =
                  ({-# LINE 21 ".\\AG/CodeGeneration.ag" #-}
                   _e1Ilabels
                   {-# LINE 919 "AG.hs" #-}
                   )
              _e2Osyms =
                  ({-# LINE 104 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 924 "AG.hs" #-}
                   )
              ( _e1Iann,_e1Icodes,_e1Ilabels) =
                  e1_ _e1Olabels _e1Osyms
              ( _e2Iann,_e2Icodes,_e2Ilabels) =
                  e2_ _e2Olabels _e2Osyms
          in  ( _lhsOann,_lhsOcodes,_lhsOlabels)))
sem_Exp_Div :: T_Exp ->
               T_Exp ->
               T_Exp
sem_Exp_Div e1_ e2_ =
    (\ _lhsIlabels
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOann :: String
              _lhsOlabels :: ([Label])
              _e1Olabels :: ([Label])
              _e1Osyms :: Syms
              _e2Olabels :: ([Label])
              _e2Osyms :: Syms
              _e1Iann :: String
              _e1Icodes :: CodeS
              _e1Ilabels :: ([Label])
              _e2Iann :: String
              _e2Icodes :: CodeS
              _e2Ilabels :: ([Label])
              _ann =
                  ({-# LINE 128 ".\\AG/CodeGeneration.ag" #-}
                   _e1Iann ++ "/"  ++ _e2Iann
                   {-# LINE 953 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 136 ".\\AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 958 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 191 ".\\AG/CodeGeneration.ag" #-}
                   _e1Icodes . _e2Icodes . div . _annote
                   {-# LINE 963 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 116 ".\\AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 968 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 ".\\AG/CodeGeneration.ag" #-}
                   _e2Ilabels
                   {-# LINE 973 "AG.hs" #-}
                   )
              _e1Olabels =
                  ({-# LINE 21 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 978 "AG.hs" #-}
                   )
              _e1Osyms =
                  ({-# LINE 104 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 983 "AG.hs" #-}
                   )
              _e2Olabels =
                  ({-# LINE 21 ".\\AG/CodeGeneration.ag" #-}
                   _e1Ilabels
                   {-# LINE 988 "AG.hs" #-}
                   )
              _e2Osyms =
                  ({-# LINE 104 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 993 "AG.hs" #-}
                   )
              ( _e1Iann,_e1Icodes,_e1Ilabels) =
                  e1_ _e1Olabels _e1Osyms
              ( _e2Iann,_e2Icodes,_e2Ilabels) =
                  e2_ _e2Olabels _e2Osyms
          in  ( _lhsOann,_lhsOcodes,_lhsOlabels)))
sem_Exp_Lt :: T_Exp ->
              T_Exp ->
              T_Exp
sem_Exp_Lt e1_ e2_ =
    (\ _lhsIlabels
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOann :: String
              _lhsOlabels :: ([Label])
              _e1Olabels :: ([Label])
              _e1Osyms :: Syms
              _e2Olabels :: ([Label])
              _e2Osyms :: Syms
              _e1Iann :: String
              _e1Icodes :: CodeS
              _e1Ilabels :: ([Label])
              _e2Iann :: String
              _e2Icodes :: CodeS
              _e2Ilabels :: ([Label])
              _ann =
                  ({-# LINE 129 ".\\AG/CodeGeneration.ag" #-}
                   _e1Iann ++ "<"  ++ _e2Iann
                   {-# LINE 1022 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 136 ".\\AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 1027 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 192 ".\\AG/CodeGeneration.ag" #-}
                   _e1Icodes . _e2Icodes . lt . _annote
                   {-# LINE 1032 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 116 ".\\AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 1037 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 ".\\AG/CodeGeneration.ag" #-}
                   _e2Ilabels
                   {-# LINE 1042 "AG.hs" #-}
                   )
              _e1Olabels =
                  ({-# LINE 21 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1047 "AG.hs" #-}
                   )
              _e1Osyms =
                  ({-# LINE 104 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1052 "AG.hs" #-}
                   )
              _e2Olabels =
                  ({-# LINE 21 ".\\AG/CodeGeneration.ag" #-}
                   _e1Ilabels
                   {-# LINE 1057 "AG.hs" #-}
                   )
              _e2Osyms =
                  ({-# LINE 104 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1062 "AG.hs" #-}
                   )
              ( _e1Iann,_e1Icodes,_e1Ilabels) =
                  e1_ _e1Olabels _e1Osyms
              ( _e2Iann,_e2Icodes,_e2Ilabels) =
                  e2_ _e2Olabels _e2Osyms
          in  ( _lhsOann,_lhsOcodes,_lhsOlabels)))
sem_Exp_Eq :: T_Exp ->
              T_Exp ->
              T_Exp
sem_Exp_Eq e1_ e2_ =
    (\ _lhsIlabels
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOann :: String
              _lhsOlabels :: ([Label])
              _e1Olabels :: ([Label])
              _e1Osyms :: Syms
              _e2Olabels :: ([Label])
              _e2Osyms :: Syms
              _e1Iann :: String
              _e1Icodes :: CodeS
              _e1Ilabels :: ([Label])
              _e2Iann :: String
              _e2Icodes :: CodeS
              _e2Ilabels :: ([Label])
              _ann =
                  ({-# LINE 130 ".\\AG/CodeGeneration.ag" #-}
                   _e1Iann ++ "==" ++ _e2Iann
                   {-# LINE 1091 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 136 ".\\AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 1096 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 193 ".\\AG/CodeGeneration.ag" #-}
                   _e1Icodes . _e2Icodes . eq . _annote
                   {-# LINE 1101 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 116 ".\\AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 1106 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 ".\\AG/CodeGeneration.ag" #-}
                   _e2Ilabels
                   {-# LINE 1111 "AG.hs" #-}
                   )
              _e1Olabels =
                  ({-# LINE 21 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1116 "AG.hs" #-}
                   )
              _e1Osyms =
                  ({-# LINE 104 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1121 "AG.hs" #-}
                   )
              _e2Olabels =
                  ({-# LINE 21 ".\\AG/CodeGeneration.ag" #-}
                   _e1Ilabels
                   {-# LINE 1126 "AG.hs" #-}
                   )
              _e2Osyms =
                  ({-# LINE 104 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1131 "AG.hs" #-}
                   )
              ( _e1Iann,_e1Icodes,_e1Ilabels) =
                  e1_ _e1Olabels _e1Osyms
              ( _e2Iann,_e2Icodes,_e2Ilabels) =
                  e2_ _e2Olabels _e2Osyms
          in  ( _lhsOann,_lhsOcodes,_lhsOlabels)))
sem_Exp_Gt :: T_Exp ->
              T_Exp ->
              T_Exp
sem_Exp_Gt e1_ e2_ =
    (\ _lhsIlabels
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOann :: String
              _lhsOlabels :: ([Label])
              _e1Olabels :: ([Label])
              _e1Osyms :: Syms
              _e2Olabels :: ([Label])
              _e2Osyms :: Syms
              _e1Iann :: String
              _e1Icodes :: CodeS
              _e1Ilabels :: ([Label])
              _e2Iann :: String
              _e2Icodes :: CodeS
              _e2Ilabels :: ([Label])
              _ann =
                  ({-# LINE 131 ".\\AG/CodeGeneration.ag" #-}
                   _e1Iann ++ ">"  ++ _e2Iann
                   {-# LINE 1160 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 136 ".\\AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 1165 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 194 ".\\AG/CodeGeneration.ag" #-}
                   _e1Icodes . _e2Icodes . gt . _annote
                   {-# LINE 1170 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 116 ".\\AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 1175 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 ".\\AG/CodeGeneration.ag" #-}
                   _e2Ilabels
                   {-# LINE 1180 "AG.hs" #-}
                   )
              _e1Olabels =
                  ({-# LINE 21 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1185 "AG.hs" #-}
                   )
              _e1Osyms =
                  ({-# LINE 104 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1190 "AG.hs" #-}
                   )
              _e2Olabels =
                  ({-# LINE 21 ".\\AG/CodeGeneration.ag" #-}
                   _e1Ilabels
                   {-# LINE 1195 "AG.hs" #-}
                   )
              _e2Osyms =
                  ({-# LINE 104 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1200 "AG.hs" #-}
                   )
              ( _e1Iann,_e1Icodes,_e1Ilabels) =
                  e1_ _e1Olabels _e1Osyms
              ( _e2Iann,_e2Icodes,_e2Ilabels) =
                  e2_ _e2Olabels _e2Osyms
          in  ( _lhsOann,_lhsOcodes,_lhsOlabels)))
-- Exps --------------------------------------------------------
type Exps = [Exp]
-- cata
sem_Exps :: Exps ->
            T_Exps
sem_Exps list =
    (Prelude.foldr sem_Exps_Cons sem_Exps_Nil (Prelude.map sem_Exp list))
-- semantic domain
type T_Exps = ([Label]) ->
              Syms ->
              ( ([String]),CodeS,([Label]))
data Inh_Exps = Inh_Exps {labels_Inh_Exps :: ([Label]),syms_Inh_Exps :: Syms}
data Syn_Exps = Syn_Exps {anns_Syn_Exps :: ([String]),codes_Syn_Exps :: CodeS,labels_Syn_Exps :: ([Label])}
wrap_Exps :: T_Exps ->
             Inh_Exps ->
             Syn_Exps
wrap_Exps sem (Inh_Exps _lhsIlabels _lhsIsyms) =
    (let ( _lhsOanns,_lhsOcodes,_lhsOlabels) = sem _lhsIlabels _lhsIsyms
     in  (Syn_Exps _lhsOanns _lhsOcodes _lhsOlabels))
sem_Exps_Cons :: T_Exp ->
                 T_Exps ->
                 T_Exps
sem_Exps_Cons hd_ tl_ =
    (\ _lhsIlabels
       _lhsIsyms ->
         (let _lhsOanns :: ([String])
              _lhsOcodes :: CodeS
              _lhsOlabels :: ([Label])
              _hdOlabels :: ([Label])
              _hdOsyms :: Syms
              _tlOlabels :: ([Label])
              _tlOsyms :: Syms
              _hdIann :: String
              _hdIcodes :: CodeS
              _hdIlabels :: ([Label])
              _tlIanns :: ([String])
              _tlIcodes :: CodeS
              _tlIlabels :: ([Label])
              _lhsOanns =
                  ({-# LINE 134 ".\\AG/CodeGeneration.ag" #-}
                   _hdIann : _tlIanns
                   {-# LINE 1248 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 143 ".\\AG/CodeGeneration.ag" #-}
                   _hdIcodes . _tlIcodes
                   {-# LINE 1253 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 ".\\AG/CodeGeneration.ag" #-}
                   _tlIlabels
                   {-# LINE 1258 "AG.hs" #-}
                   )
              _hdOlabels =
                  ({-# LINE 21 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1263 "AG.hs" #-}
                   )
              _hdOsyms =
                  ({-# LINE 104 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1268 "AG.hs" #-}
                   )
              _tlOlabels =
                  ({-# LINE 21 ".\\AG/CodeGeneration.ag" #-}
                   _hdIlabels
                   {-# LINE 1273 "AG.hs" #-}
                   )
              _tlOsyms =
                  ({-# LINE 104 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1278 "AG.hs" #-}
                   )
              ( _hdIann,_hdIcodes,_hdIlabels) =
                  hd_ _hdOlabels _hdOsyms
              ( _tlIanns,_tlIcodes,_tlIlabels) =
                  tl_ _tlOlabels _tlOsyms
          in  ( _lhsOanns,_lhsOcodes,_lhsOlabels)))
sem_Exps_Nil :: T_Exps
sem_Exps_Nil =
    (\ _lhsIlabels
       _lhsIsyms ->
         (let _lhsOanns :: ([String])
              _lhsOcodes :: CodeS
              _lhsOlabels :: ([Label])
              _lhsOanns =
                  ({-# LINE 133 ".\\AG/CodeGeneration.ag" #-}
                   []
                   {-# LINE 1295 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 143 ".\\AG/CodeGeneration.ag" #-}
                   id
                   {-# LINE 1300 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1305 "AG.hs" #-}
                   )
          in  ( _lhsOanns,_lhsOcodes,_lhsOlabels)))
-- Prog --------------------------------------------------------
data Prog = TopLevelDecls (Decls)
-- cata
sem_Prog :: Prog ->
            T_Prog
sem_Prog (TopLevelDecls _ds) =
    (sem_Prog_TopLevelDecls (sem_Decls _ds))
-- semantic domain
type T_Prog = ( Code)
data Inh_Prog = Inh_Prog {}
data Syn_Prog = Syn_Prog {code_Syn_Prog :: Code}
wrap_Prog :: T_Prog ->
             Inh_Prog ->
             Syn_Prog
wrap_Prog sem (Inh_Prog) =
    (let ( _lhsOcode) = sem
     in  (Syn_Prog _lhsOcode))
sem_Prog_TopLevelDecls :: T_Decls ->
                          T_Prog
sem_Prog_TopLevelDecls ds_ =
    (let _dsOlabels :: ([Label])
         _dsOoffset :: Int
         _dsOsyms :: Syms
         _lhsOcode :: Code
         _dsIcodes :: CodeS
         _dsIenv :: Env
         _dsIlabels :: ([Label])
         _dsIoffset :: Int
         _dsOlabels =
             ({-# LINE 24 ".\\AG/CodeGeneration.ag" #-}
              [0 ..]
              {-# LINE 1339 "AG.hs" #-}
              )
         _dsOoffset =
             ({-# LINE 45 ".\\AG/CodeGeneration.ag" #-}
              1
              {-# LINE 1344 "AG.hs" #-}
              )
         _dsOsyms =
             ({-# LINE 106 ".\\AG/CodeGeneration.ag" #-}
              [_dsIenv]
              {-# LINE 1349 "AG.hs" #-}
              )
         _codes =
             ({-# LINE 145 ".\\AG/CodeGeneration.ag" #-}
              _dsIcodes .
              enter _dsIenv .
              call "main" [_dsIenv] .
              ajs (- 1) .
              exit _dsIenv
              {-# LINE 1358 "AG.hs" #-}
              )
         _lhsOcode =
             ({-# LINE 199 ".\\AG/CodeGeneration.ag" #-}
              Code (_codes     [])
              {-# LINE 1363 "AG.hs" #-}
              )
         ( _dsIcodes,_dsIenv,_dsIlabels,_dsIoffset) =
             ds_ _dsOlabels _dsOoffset _dsOsyms
     in  ( _lhsOcode))
-- Stmt --------------------------------------------------------
data Stmt = Empty
          | Decl (Decl)
          | Assign (Ident) (Exp)
          | Call_ (Ident) (Exps)
          | Print (Exp)
          | Return (Exp)
          | If (Exp) (Stmt) (Stmt)
          | Block (Stmts)
-- cata
sem_Stmt :: Stmt ->
            T_Stmt
sem_Stmt (Empty) =
    (sem_Stmt_Empty)
sem_Stmt (Decl _d) =
    (sem_Stmt_Decl (sem_Decl _d))
sem_Stmt (Assign _x _e) =
    (sem_Stmt_Assign _x (sem_Exp _e))
sem_Stmt (Call_ _f _es) =
    (sem_Stmt_Call_ _f (sem_Exps _es))
sem_Stmt (Print _e) =
    (sem_Stmt_Print (sem_Exp _e))
sem_Stmt (Return _e) =
    (sem_Stmt_Return (sem_Exp _e))
sem_Stmt (If _e _s1 _s2) =
    (sem_Stmt_If (sem_Exp _e) (sem_Stmt _s1) (sem_Stmt _s2))
sem_Stmt (Block _b) =
    (sem_Stmt_Block (sem_Stmts _b))
-- semantic domain
type T_Stmt = ([Label]) ->
              Int ->
              Syms ->
              ( CodeS,Env,([Label]),Int)
data Inh_Stmt = Inh_Stmt {labels_Inh_Stmt :: ([Label]),offset_Inh_Stmt :: Int,syms_Inh_Stmt :: Syms}
data Syn_Stmt = Syn_Stmt {codes_Syn_Stmt :: CodeS,env_Syn_Stmt :: Env,labels_Syn_Stmt :: ([Label]),offset_Syn_Stmt :: Int}
wrap_Stmt :: T_Stmt ->
             Inh_Stmt ->
             Syn_Stmt
wrap_Stmt sem (Inh_Stmt _lhsIlabels _lhsIoffset _lhsIsyms) =
    (let ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset) = sem _lhsIlabels _lhsIoffset _lhsIsyms
     in  (Syn_Stmt _lhsOcodes _lhsOenv _lhsOlabels _lhsOoffset))
sem_Stmt_Empty :: T_Stmt
sem_Stmt_Empty =
    (\ _lhsIlabels
       _lhsIoffset
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOenv :: Env
              _lhsOlabels :: ([Label])
              _lhsOoffset :: Int
              _lhsOcodes =
                  ({-# LINE 143 ".\\AG/CodeGeneration.ag" #-}
                   id
                   {-# LINE 1421 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 73 ".\\AG/CodeGeneration.ag" #-}
                   []
                   {-# LINE 1426 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1431 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 43 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1436 "AG.hs" #-}
                   )
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset)))
sem_Stmt_Decl :: T_Decl ->
                 T_Stmt
sem_Stmt_Decl d_ =
    (\ _lhsIlabels
       _lhsIoffset
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOenv :: Env
              _lhsOlabels :: ([Label])
              _lhsOoffset :: Int
              _dOlabels :: ([Label])
              _dOoffset :: Int
              _dOsyms :: Syms
              _dIcodes :: CodeS
              _dIenv :: Env
              _dIlabels :: ([Label])
              _dIoffset :: Int
              _lhsOcodes =
                  ({-# LINE 143 ".\\AG/CodeGeneration.ag" #-}
                   _dIcodes
                   {-# LINE 1459 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 73 ".\\AG/CodeGeneration.ag" #-}
                   _dIenv
                   {-# LINE 1464 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 ".\\AG/CodeGeneration.ag" #-}
                   _dIlabels
                   {-# LINE 1469 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 43 ".\\AG/CodeGeneration.ag" #-}
                   _dIoffset
                   {-# LINE 1474 "AG.hs" #-}
                   )
              _dOlabels =
                  ({-# LINE 21 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1479 "AG.hs" #-}
                   )
              _dOoffset =
                  ({-# LINE 42 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1484 "AG.hs" #-}
                   )
              _dOsyms =
                  ({-# LINE 104 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1489 "AG.hs" #-}
                   )
              ( _dIcodes,_dIenv,_dIlabels,_dIoffset) =
                  d_ _dOlabels _dOoffset _dOsyms
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset)))
sem_Stmt_Assign :: Ident ->
                   T_Exp ->
                   T_Stmt
sem_Stmt_Assign x_ e_ =
    (\ _lhsIlabels
       _lhsIoffset
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOenv :: Env
              _lhsOlabels :: ([Label])
              _lhsOoffset :: Int
              _eOlabels :: ([Label])
              _eOsyms :: Syms
              _eIann :: String
              _eIcodes :: CodeS
              _eIlabels :: ([Label])
              _lhsOcodes =
                  ({-# LINE 163 ".\\AG/CodeGeneration.ag" #-}
                   _eIcodes . set x_ _lhsIsyms
                   {-# LINE 1513 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 73 ".\\AG/CodeGeneration.ag" #-}
                   []
                   {-# LINE 1518 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 ".\\AG/CodeGeneration.ag" #-}
                   _eIlabels
                   {-# LINE 1523 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 43 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1528 "AG.hs" #-}
                   )
              _eOlabels =
                  ({-# LINE 21 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1533 "AG.hs" #-}
                   )
              _eOsyms =
                  ({-# LINE 104 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1538 "AG.hs" #-}
                   )
              ( _eIann,_eIcodes,_eIlabels) =
                  e_ _eOlabels _eOsyms
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset)))
sem_Stmt_Call_ :: Ident ->
                  T_Exps ->
                  T_Stmt
sem_Stmt_Call_ f_ es_ =
    (\ _lhsIlabels
       _lhsIoffset
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOenv :: Env
              _lhsOlabels :: ([Label])
              _lhsOoffset :: Int
              _esOlabels :: ([Label])
              _esOsyms :: Syms
              _esIanns :: ([String])
              _esIcodes :: CodeS
              _esIlabels :: ([Label])
              _lhsOcodes =
                  ({-# LINE 164 ".\\AG/CodeGeneration.ag" #-}
                   wrapSLCacheLoader _lhsIsyms
                    (_esIcodes .
                     call f_ _lhsIsyms) .
                   ajs (- 1)
                   {-# LINE 1565 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 73 ".\\AG/CodeGeneration.ag" #-}
                   []
                   {-# LINE 1570 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 ".\\AG/CodeGeneration.ag" #-}
                   _esIlabels
                   {-# LINE 1575 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 43 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1580 "AG.hs" #-}
                   )
              _esOlabels =
                  ({-# LINE 21 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1585 "AG.hs" #-}
                   )
              _esOsyms =
                  ({-# LINE 104 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1590 "AG.hs" #-}
                   )
              ( _esIanns,_esIcodes,_esIlabels) =
                  es_ _esOlabels _esOsyms
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset)))
sem_Stmt_Print :: T_Exp ->
                  T_Stmt
sem_Stmt_Print e_ =
    (\ _lhsIlabels
       _lhsIoffset
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOenv :: Env
              _lhsOlabels :: ([Label])
              _lhsOoffset :: Int
              _eOlabels :: ([Label])
              _eOsyms :: Syms
              _eIann :: String
              _eIcodes :: CodeS
              _eIlabels :: ([Label])
              _lhsOcodes =
                  ({-# LINE 168 ".\\AG/CodeGeneration.ag" #-}
                   _eIcodes . trap 0
                   {-# LINE 1613 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 73 ".\\AG/CodeGeneration.ag" #-}
                   []
                   {-# LINE 1618 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 ".\\AG/CodeGeneration.ag" #-}
                   _eIlabels
                   {-# LINE 1623 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 43 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1628 "AG.hs" #-}
                   )
              _eOlabels =
                  ({-# LINE 21 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1633 "AG.hs" #-}
                   )
              _eOsyms =
                  ({-# LINE 104 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1638 "AG.hs" #-}
                   )
              ( _eIann,_eIcodes,_eIlabels) =
                  e_ _eOlabels _eOsyms
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset)))
sem_Stmt_Return :: T_Exp ->
                   T_Stmt
sem_Stmt_Return e_ =
    (\ _lhsIlabels
       _lhsIoffset
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOenv :: Env
              _lhsOlabels :: ([Label])
              _lhsOoffset :: Int
              _eOlabels :: ([Label])
              _eOsyms :: Syms
              _eIann :: String
              _eIcodes :: CodeS
              _eIlabels :: ([Label])
              _lhsOcodes =
                  ({-# LINE 169 ".\\AG/CodeGeneration.ag" #-}
                   _eIcodes . return_ _lhsIsyms
                   {-# LINE 1661 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 73 ".\\AG/CodeGeneration.ag" #-}
                   []
                   {-# LINE 1666 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 ".\\AG/CodeGeneration.ag" #-}
                   _eIlabels
                   {-# LINE 1671 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 43 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1676 "AG.hs" #-}
                   )
              _eOlabels =
                  ({-# LINE 21 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1681 "AG.hs" #-}
                   )
              _eOsyms =
                  ({-# LINE 104 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1686 "AG.hs" #-}
                   )
              ( _eIann,_eIcodes,_eIlabels) =
                  e_ _eOlabels _eOsyms
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset)))
sem_Stmt_If :: T_Exp ->
               T_Stmt ->
               T_Stmt ->
               T_Stmt
sem_Stmt_If e_ s1_ s2_ =
    (\ _lhsIlabels
       _lhsIoffset
       _lhsIsyms ->
         (let _eOlabels :: ([Label])
              _lhsOcodes :: CodeS
              _lhsOenv :: Env
              _lhsOlabels :: ([Label])
              _lhsOoffset :: Int
              _eOsyms :: Syms
              _s1Olabels :: ([Label])
              _s1Ooffset :: Int
              _s1Osyms :: Syms
              _s2Olabels :: ([Label])
              _s2Ooffset :: Int
              _s2Osyms :: Syms
              _eIann :: String
              _eIcodes :: CodeS
              _eIlabels :: ([Label])
              _s1Icodes :: CodeS
              _s1Ienv :: Env
              _s1Ilabels :: ([Label])
              _s1Ioffset :: Int
              _s2Icodes :: CodeS
              _s2Ienv :: Env
              _s2Ilabels :: ([Label])
              _s2Ioffset :: Int
              _elseLabel =
                  ({-# LINE 30 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIlabels !! 0
                   {-# LINE 1725 "AG.hs" #-}
                   )
              _fiLabel =
                  ({-# LINE 31 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIlabels !! 1
                   {-# LINE 1730 "AG.hs" #-}
                   )
              _eOlabels =
                  ({-# LINE 32 ".\\AG/CodeGeneration.ag" #-}
                   drop 2 _lhsIlabels
                   {-# LINE 1735 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 170 ".\\AG/CodeGeneration.ag" #-}
                   _eIcodes .
                   brf _elseLabel     .
                   _s1Icodes .
                   bra _fiLabel     .
                   label _elseLabel     .
                     _s2Icodes .
                   label _fiLabel
                   {-# LINE 1746 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 73 ".\\AG/CodeGeneration.ag" #-}
                   _s1Ienv ++ _s2Ienv
                   {-# LINE 1751 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 ".\\AG/CodeGeneration.ag" #-}
                   _s2Ilabels
                   {-# LINE 1756 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 43 ".\\AG/CodeGeneration.ag" #-}
                   _s2Ioffset
                   {-# LINE 1761 "AG.hs" #-}
                   )
              _eOsyms =
                  ({-# LINE 104 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1766 "AG.hs" #-}
                   )
              _s1Olabels =
                  ({-# LINE 21 ".\\AG/CodeGeneration.ag" #-}
                   _eIlabels
                   {-# LINE 1771 "AG.hs" #-}
                   )
              _s1Ooffset =
                  ({-# LINE 42 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1776 "AG.hs" #-}
                   )
              _s1Osyms =
                  ({-# LINE 104 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1781 "AG.hs" #-}
                   )
              _s2Olabels =
                  ({-# LINE 21 ".\\AG/CodeGeneration.ag" #-}
                   _s1Ilabels
                   {-# LINE 1786 "AG.hs" #-}
                   )
              _s2Ooffset =
                  ({-# LINE 42 ".\\AG/CodeGeneration.ag" #-}
                   _s1Ioffset
                   {-# LINE 1791 "AG.hs" #-}
                   )
              _s2Osyms =
                  ({-# LINE 104 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1796 "AG.hs" #-}
                   )
              ( _eIann,_eIcodes,_eIlabels) =
                  e_ _eOlabels _eOsyms
              ( _s1Icodes,_s1Ienv,_s1Ilabels,_s1Ioffset) =
                  s1_ _s1Olabels _s1Ooffset _s1Osyms
              ( _s2Icodes,_s2Ienv,_s2Ilabels,_s2Ioffset) =
                  s2_ _s2Olabels _s2Ooffset _s2Osyms
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset)))
sem_Stmt_Block :: T_Stmts ->
                  T_Stmt
sem_Stmt_Block b_ =
    (\ _lhsIlabels
       _lhsIoffset
       _lhsIsyms ->
         (let _lhsOoffset :: Int
              _lhsOenv :: Env
              _bOsyms :: Syms
              _lhsOcodes :: CodeS
              _lhsOlabels :: ([Label])
              _bOlabels :: ([Label])
              _bOoffset :: Int
              _bIcodes :: CodeS
              _bIenv :: Env
              _bIlabels :: ([Label])
              _bIoffset :: Int
              _lhsOoffset =
                  ({-# LINE 48 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1825 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 78 ".\\AG/CodeGeneration.ag" #-}
                   []
                   {-# LINE 1830 "AG.hs" #-}
                   )
              _bOsyms =
                  ({-# LINE 108 ".\\AG/CodeGeneration.ag" #-}
                   let local : global = _lhsIsyms
                   in  (local ++ _bIenv) : global
                   {-# LINE 1836 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 177 ".\\AG/CodeGeneration.ag" #-}
                   enter _bIenv .
                   _bIcodes .
                   exit _bIenv
                   {-# LINE 1843 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 ".\\AG/CodeGeneration.ag" #-}
                   _bIlabels
                   {-# LINE 1848 "AG.hs" #-}
                   )
              _bOlabels =
                  ({-# LINE 21 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1853 "AG.hs" #-}
                   )
              _bOoffset =
                  ({-# LINE 42 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1858 "AG.hs" #-}
                   )
              ( _bIcodes,_bIenv,_bIlabels,_bIoffset) =
                  b_ _bOlabels _bOoffset _bOsyms
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset)))
-- Stmts -------------------------------------------------------
type Stmts = [Stmt]
-- cata
sem_Stmts :: Stmts ->
             T_Stmts
sem_Stmts list =
    (Prelude.foldr sem_Stmts_Cons sem_Stmts_Nil (Prelude.map sem_Stmt list))
-- semantic domain
type T_Stmts = ([Label]) ->
               Int ->
               Syms ->
               ( CodeS,Env,([Label]),Int)
data Inh_Stmts = Inh_Stmts {labels_Inh_Stmts :: ([Label]),offset_Inh_Stmts :: Int,syms_Inh_Stmts :: Syms}
data Syn_Stmts = Syn_Stmts {codes_Syn_Stmts :: CodeS,env_Syn_Stmts :: Env,labels_Syn_Stmts :: ([Label]),offset_Syn_Stmts :: Int}
wrap_Stmts :: T_Stmts ->
              Inh_Stmts ->
              Syn_Stmts
wrap_Stmts sem (Inh_Stmts _lhsIlabels _lhsIoffset _lhsIsyms) =
    (let ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset) = sem _lhsIlabels _lhsIoffset _lhsIsyms
     in  (Syn_Stmts _lhsOcodes _lhsOenv _lhsOlabels _lhsOoffset))
sem_Stmts_Cons :: T_Stmt ->
                  T_Stmts ->
                  T_Stmts
sem_Stmts_Cons hd_ tl_ =
    (\ _lhsIlabels
       _lhsIoffset
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOenv :: Env
              _lhsOlabels :: ([Label])
              _lhsOoffset :: Int
              _hdOlabels :: ([Label])
              _hdOoffset :: Int
              _hdOsyms :: Syms
              _tlOlabels :: ([Label])
              _tlOoffset :: Int
              _tlOsyms :: Syms
              _hdIcodes :: CodeS
              _hdIenv :: Env
              _hdIlabels :: ([Label])
              _hdIoffset :: Int
              _tlIcodes :: CodeS
              _tlIenv :: Env
              _tlIlabels :: ([Label])
              _tlIoffset :: Int
              _lhsOcodes =
                  ({-# LINE 143 ".\\AG/CodeGeneration.ag" #-}
                   _hdIcodes . _tlIcodes
                   {-# LINE 1911 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 73 ".\\AG/CodeGeneration.ag" #-}
                   _hdIenv ++ _tlIenv
                   {-# LINE 1916 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 ".\\AG/CodeGeneration.ag" #-}
                   _tlIlabels
                   {-# LINE 1921 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 43 ".\\AG/CodeGeneration.ag" #-}
                   _tlIoffset
                   {-# LINE 1926 "AG.hs" #-}
                   )
              _hdOlabels =
                  ({-# LINE 21 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1931 "AG.hs" #-}
                   )
              _hdOoffset =
                  ({-# LINE 42 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1936 "AG.hs" #-}
                   )
              _hdOsyms =
                  ({-# LINE 104 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1941 "AG.hs" #-}
                   )
              _tlOlabels =
                  ({-# LINE 21 ".\\AG/CodeGeneration.ag" #-}
                   _hdIlabels
                   {-# LINE 1946 "AG.hs" #-}
                   )
              _tlOoffset =
                  ({-# LINE 42 ".\\AG/CodeGeneration.ag" #-}
                   _hdIoffset
                   {-# LINE 1951 "AG.hs" #-}
                   )
              _tlOsyms =
                  ({-# LINE 104 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1956 "AG.hs" #-}
                   )
              ( _hdIcodes,_hdIenv,_hdIlabels,_hdIoffset) =
                  hd_ _hdOlabels _hdOoffset _hdOsyms
              ( _tlIcodes,_tlIenv,_tlIlabels,_tlIoffset) =
                  tl_ _tlOlabels _tlOoffset _tlOsyms
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset)))
sem_Stmts_Nil :: T_Stmts
sem_Stmts_Nil =
    (\ _lhsIlabels
       _lhsIoffset
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOenv :: Env
              _lhsOlabels :: ([Label])
              _lhsOoffset :: Int
              _lhsOcodes =
                  ({-# LINE 143 ".\\AG/CodeGeneration.ag" #-}
                   id
                   {-# LINE 1975 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 73 ".\\AG/CodeGeneration.ag" #-}
                   []
                   {-# LINE 1980 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1985 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 43 ".\\AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1990 "AG.hs" #-}
                   )
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset)))