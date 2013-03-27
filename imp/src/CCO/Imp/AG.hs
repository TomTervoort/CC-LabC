

-- UUAGC 0.9.38.1 (AG.ag)
module CCO.Imp.AG where

{-# LINE 2 "./AG/CodeGeneration.ag" #-}

import CCO.Ssm hiding (Add, Sub, Mul, Div, Eq, Lt, Gt)
import Prelude hiding (div)

import Data.Maybe
import Control.Arrow
import Data.List
import Data.Ord

import Debug.Trace
{-# LINE 18 "AG.hs" #-}
{-# LINE 5 "./AG/Base.ag" #-}

type Ident = String    -- ^ Type of identifiers.
{-# LINE 22 "AG.hs" #-}

{-# LINE 54 "./AG/CodeGeneration.ag" #-}

-- | An environment maps identifiers to symbol descriptors.
type Env = [(Ident, Sym)]

-- | A symbol descriptor either describes a variable or a function symbol.
-- For a variable, we store its offset relative to the mark pointer; for
-- a function we store its begin label.
data Sym = V Int | F Int

-- | Restrict environments to a particular type of descriptor.
vars   env = [entry | entry@(_, V _     ) <- env            ]
funs   env = [entry | entry@(_, F _     ) <- env            ]
params env = [entry | entry@(_, V offset) <- env, offset < 0]
{-# LINE 38 "AG.hs" #-}

{-# LINE 89 "./AG/CodeGeneration.ag" #-}

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

{-# LINE 205 "./AG/CodeGeneration.ag" #-}

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

{-- | Produces code for retrieving the value of a global variable.
getGlobal :: Ident -> Syms -> CodeS
getGlobal x []           = error ("unknown variable: " ++ x)
getGlobal x (env : envs) = case lookup x (vars env) of
  Nothing         -> lda (- 2) . getGlobal x envs
  Just (V offset) -> lda offset --}

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

{-- | Produces code for assigning a new value to a global variable.
setGlobal :: Ident -> Syms -> CodeS
setGlobal x []           = error ("unknown variable: " ++ x)
setGlobal x (env : envs) = case lookup x (vars env) of
  Nothing         -> lda (- 2) . setGlobal x envs
  Just (V offset) -> sta offset --}

-- | Produces code for calling a function.
call :: Ident -> Syms -> CodeS
call f (local : global) = case lookup f (funs local) of
  Nothing             -> ldl (- 2) . callGlobal f global
  Just (F beginLabel) -> ldr MP . ldcL beginLabel . jsr 
                          

-- | Produces code for calling a global function.
callGlobal :: Ident -> Syms -> CodeS
callGlobal f []           = error ("unknown function: " ++ f)
callGlobal f (env : envs) = case lookup f (funs env) of
  Nothing             -> lda (- 2) . callGlobal f envs
  Just (F beginLabel) -> ldcL beginLabel . jsr

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

-- | Based on local and global environments, this gives a list of non-local variables that may be 
--   used and should therefore be accessible through the static link cache.
cacheVars :: Env -> Syms -> [Ident]
cacheVars local global = concatMap (map (filter isRequired . fst) . vars) global
 where isRequired _ = True

{-# LINE 189 "AG.hs" #-}
-- Decl --------------------------------------------------------
data Decl  = FunDecl (Ident) (([Ident])) (Stmts ) 
           | VarDecl (Ident) 
-- cata
sem_Decl :: Decl  ->
            T_Decl 
sem_Decl (FunDecl _f _xs _b )  =
    (sem_Decl_FunDecl _f _xs (sem_Stmts _b ) )
sem_Decl (VarDecl _x )  =
    (sem_Decl_VarDecl _x )
-- semantic domain
type T_Decl  = ([Label]) ->
               Int ->
               Syms ->
               ( CodeS,Env,([Label]),Int)
data Inh_Decl  = Inh_Decl {labels_Inh_Decl :: ([Label]),offset_Inh_Decl :: Int,syms_Inh_Decl :: Syms}
data Syn_Decl  = Syn_Decl {codes_Syn_Decl :: CodeS,env_Syn_Decl :: Env,labels_Syn_Decl :: ([Label]),offset_Syn_Decl :: Int}
wrap_Decl :: T_Decl  ->
             Inh_Decl  ->
             Syn_Decl 
wrap_Decl sem (Inh_Decl _lhsIlabels _lhsIoffset _lhsIsyms )  =
    (let ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset) = sem _lhsIlabels _lhsIoffset _lhsIsyms 
     in  (Syn_Decl _lhsOcodes _lhsOenv _lhsOlabels _lhsOoffset ))
sem_Decl_FunDecl :: Ident ->
                    ([Ident]) ->
                    T_Stmts  ->
                    T_Decl 
sem_Decl_FunDecl f_ xs_ b_  =
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
                  ({-# LINE 26 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels !! 0
                   {-# LINE 235 "AG.hs" #-}
                   )
              _endLabel =
                  ({-# LINE 27 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels !! 1
                   {-# LINE 240 "AG.hs" #-}
                   )
              _bOlabels =
                  ({-# LINE 28 "./AG/CodeGeneration.ag" #-}
                   drop 2 _lhsIlabels
                   {-# LINE 245 "AG.hs" #-}
                   )
              _bOoffset =
                  ({-# LINE 47 "./AG/CodeGeneration.ag" #-}
                   1
                   {-# LINE 250 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 76 "./AG/CodeGeneration.ag" #-}
                   [(f_, F _beginLabel    )]
                   {-# LINE 255 "AG.hs" #-}
                   )
              _params =
                  ({-# LINE 83 "./AG/CodeGeneration.ag" #-}
                   zipWith (\x i -> (x, V i)) xs_ [- (2 + length xs_) ..]
                   {-# LINE 260 "AG.hs" #-}
                   )
              _bOsyms =
                  ({-# LINE 107 "./AG/CodeGeneration.ag" #-}
                   (_params     ++ _bIenv) : _lhsIsyms
                   {-# LINE 265 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 151 "./AG/CodeGeneration.ag" #-}
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
                   {-# LINE 280 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _bIlabels
                   {-# LINE 285 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 43 "./AG/CodeGeneration.ag" #-}
                   _bIoffset
                   {-# LINE 290 "AG.hs" #-}
                   )
              ( _bIcodes,_bIenv,_bIlabels,_bIoffset) =
                  b_ _bOlabels _bOoffset _bOsyms 
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset)))
sem_Decl_VarDecl :: Ident ->
                    T_Decl 
sem_Decl_VarDecl x_  =
    (\ _lhsIlabels
       _lhsIoffset
       _lhsIsyms ->
         (let _lhsOoffset :: Int
              _lhsOenv :: Env
              _lhsOcodes :: CodeS
              _lhsOlabels :: ([Label])
              _lhsOoffset =
                  ({-# LINE 46 "./AG/CodeGeneration.ag" #-}
                   _lhsIoffset + 1
                   {-# LINE 308 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 75 "./AG/CodeGeneration.ag" #-}
                   [(x_, V _lhsIoffset    )]
                   {-# LINE 313 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 143 "./AG/CodeGeneration.ag" #-}
                   id
                   {-# LINE 318 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 323 "AG.hs" #-}
                   )
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset)))
-- Decls -------------------------------------------------------
type Decls  = [Decl ]
-- cata
sem_Decls :: Decls  ->
             T_Decls 
sem_Decls list  =
    (Prelude.foldr sem_Decls_Cons sem_Decls_Nil (Prelude.map sem_Decl list) )
-- semantic domain
type T_Decls  = ([Label]) ->
                Int ->
                Syms ->
                ( CodeS,Env,([Label]),Int)
data Inh_Decls  = Inh_Decls {labels_Inh_Decls :: ([Label]),offset_Inh_Decls :: Int,syms_Inh_Decls :: Syms}
data Syn_Decls  = Syn_Decls {codes_Syn_Decls :: CodeS,env_Syn_Decls :: Env,labels_Syn_Decls :: ([Label]),offset_Syn_Decls :: Int}
wrap_Decls :: T_Decls  ->
              Inh_Decls  ->
              Syn_Decls 
wrap_Decls sem (Inh_Decls _lhsIlabels _lhsIoffset _lhsIsyms )  =
    (let ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset) = sem _lhsIlabels _lhsIoffset _lhsIsyms 
     in  (Syn_Decls _lhsOcodes _lhsOenv _lhsOlabels _lhsOoffset ))
sem_Decls_Cons :: T_Decl  ->
                  T_Decls  ->
                  T_Decls 
sem_Decls_Cons hd_ tl_  =
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
                  ({-# LINE 143 "./AG/CodeGeneration.ag" #-}
                   _hdIcodes . _tlIcodes
                   {-# LINE 374 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 73 "./AG/CodeGeneration.ag" #-}
                   _hdIenv ++ _tlIenv
                   {-# LINE 379 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _tlIlabels
                   {-# LINE 384 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 43 "./AG/CodeGeneration.ag" #-}
                   _tlIoffset
                   {-# LINE 389 "AG.hs" #-}
                   )
              _hdOlabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 394 "AG.hs" #-}
                   )
              _hdOoffset =
                  ({-# LINE 42 "./AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 399 "AG.hs" #-}
                   )
              _hdOsyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 404 "AG.hs" #-}
                   )
              _tlOlabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _hdIlabels
                   {-# LINE 409 "AG.hs" #-}
                   )
              _tlOoffset =
                  ({-# LINE 42 "./AG/CodeGeneration.ag" #-}
                   _hdIoffset
                   {-# LINE 414 "AG.hs" #-}
                   )
              _tlOsyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 419 "AG.hs" #-}
                   )
              ( _hdIcodes,_hdIenv,_hdIlabels,_hdIoffset) =
                  hd_ _hdOlabels _hdOoffset _hdOsyms 
              ( _tlIcodes,_tlIenv,_tlIlabels,_tlIoffset) =
                  tl_ _tlOlabels _tlOoffset _tlOsyms 
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset)))
sem_Decls_Nil :: T_Decls 
sem_Decls_Nil  =
    (\ _lhsIlabels
       _lhsIoffset
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOenv :: Env
              _lhsOlabels :: ([Label])
              _lhsOoffset :: Int
              _lhsOcodes =
                  ({-# LINE 143 "./AG/CodeGeneration.ag" #-}
                   id
                   {-# LINE 438 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 73 "./AG/CodeGeneration.ag" #-}
                   []
                   {-# LINE 443 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 448 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 43 "./AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 453 "AG.hs" #-}
                   )
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset)))
-- Exp ---------------------------------------------------------
data Exp  = Add (Exp ) (Exp ) 
          | Call (Ident) (Exps ) 
          | Div (Exp ) (Exp ) 
          | Eq (Exp ) (Exp ) 
          | False_ 
          | Gt (Exp ) (Exp ) 
          | Int (Int) 
          | Lt (Exp ) (Exp ) 
          | Mul (Exp ) (Exp ) 
          | Sub (Exp ) (Exp ) 
          | True_ 
          | Var (Ident) 
-- cata
sem_Exp :: Exp  ->
           T_Exp 
sem_Exp (Add _e1 _e2 )  =
    (sem_Exp_Add (sem_Exp _e1 ) (sem_Exp _e2 ) )
sem_Exp (Call _f _es )  =
    (sem_Exp_Call _f (sem_Exps _es ) )
sem_Exp (Div _e1 _e2 )  =
    (sem_Exp_Div (sem_Exp _e1 ) (sem_Exp _e2 ) )
sem_Exp (Eq _e1 _e2 )  =
    (sem_Exp_Eq (sem_Exp _e1 ) (sem_Exp _e2 ) )
sem_Exp (False_ )  =
    (sem_Exp_False_ )
sem_Exp (Gt _e1 _e2 )  =
    (sem_Exp_Gt (sem_Exp _e1 ) (sem_Exp _e2 ) )
sem_Exp (Int _n )  =
    (sem_Exp_Int _n )
sem_Exp (Lt _e1 _e2 )  =
    (sem_Exp_Lt (sem_Exp _e1 ) (sem_Exp _e2 ) )
sem_Exp (Mul _e1 _e2 )  =
    (sem_Exp_Mul (sem_Exp _e1 ) (sem_Exp _e2 ) )
sem_Exp (Sub _e1 _e2 )  =
    (sem_Exp_Sub (sem_Exp _e1 ) (sem_Exp _e2 ) )
sem_Exp (True_ )  =
    (sem_Exp_True_ )
sem_Exp (Var _x )  =
    (sem_Exp_Var _x )
-- semantic domain
type T_Exp  = ([Label]) ->
              Syms ->
              ( String,CodeS,([Label]))
data Inh_Exp  = Inh_Exp {labels_Inh_Exp :: ([Label]),syms_Inh_Exp :: Syms}
data Syn_Exp  = Syn_Exp {ann_Syn_Exp :: String,codes_Syn_Exp :: CodeS,labels_Syn_Exp :: ([Label])}
wrap_Exp :: T_Exp  ->
            Inh_Exp  ->
            Syn_Exp 
wrap_Exp sem (Inh_Exp _lhsIlabels _lhsIsyms )  =
    (let ( _lhsOann,_lhsOcodes,_lhsOlabels) = sem _lhsIlabels _lhsIsyms 
     in  (Syn_Exp _lhsOann _lhsOcodes _lhsOlabels ))
sem_Exp_Add :: T_Exp  ->
               T_Exp  ->
               T_Exp 
sem_Exp_Add e1_ e2_  =
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
                  ({-# LINE 125 "./AG/CodeGeneration.ag" #-}
                   _e1Iann ++ "+"  ++ _e2Iann
                   {-# LINE 530 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 136 "./AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 535 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 188 "./AG/CodeGeneration.ag" #-}
                   _e1Icodes . _e2Icodes . add . _annote
                   {-# LINE 540 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 116 "./AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 545 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _e2Ilabels
                   {-# LINE 550 "AG.hs" #-}
                   )
              _e1Olabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 555 "AG.hs" #-}
                   )
              _e1Osyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 560 "AG.hs" #-}
                   )
              _e2Olabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _e1Ilabels
                   {-# LINE 565 "AG.hs" #-}
                   )
              _e2Osyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 570 "AG.hs" #-}
                   )
              ( _e1Iann,_e1Icodes,_e1Ilabels) =
                  e1_ _e1Olabels _e1Osyms 
              ( _e2Iann,_e2Icodes,_e2Ilabels) =
                  e2_ _e2Olabels _e2Osyms 
          in  ( _lhsOann,_lhsOcodes,_lhsOlabels)))
sem_Exp_Call :: Ident ->
                T_Exps  ->
                T_Exp 
sem_Exp_Call f_ es_  =
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
                  ({-# LINE 124 "./AG/CodeGeneration.ag" #-}
                   f_ ++ "(" ++ concat (intersperse "," _esIanns) ++ ")"
                   {-# LINE 594 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 136 "./AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 599 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 185 "./AG/CodeGeneration.ag" #-}
                   wrapSLCacheLoader _lhsIsyms
                    (_esIcodes .
                     call f_ _lhsIsyms)
                   {-# LINE 606 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 116 "./AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 611 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _esIlabels
                   {-# LINE 616 "AG.hs" #-}
                   )
              _esOlabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 621 "AG.hs" #-}
                   )
              _esOsyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 626 "AG.hs" #-}
                   )
              ( _esIanns,_esIcodes,_esIlabels) =
                  es_ _esOlabels _esOsyms 
          in  ( _lhsOann,_lhsOcodes,_lhsOlabels)))
sem_Exp_Div :: T_Exp  ->
               T_Exp  ->
               T_Exp 
sem_Exp_Div e1_ e2_  =
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
                  ({-# LINE 128 "./AG/CodeGeneration.ag" #-}
                   _e1Iann ++ "/"  ++ _e2Iann
                   {-# LINE 653 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 136 "./AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 658 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 191 "./AG/CodeGeneration.ag" #-}
                   _e1Icodes . _e2Icodes . div . _annote
                   {-# LINE 663 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 116 "./AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 668 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _e2Ilabels
                   {-# LINE 673 "AG.hs" #-}
                   )
              _e1Olabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 678 "AG.hs" #-}
                   )
              _e1Osyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 683 "AG.hs" #-}
                   )
              _e2Olabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _e1Ilabels
                   {-# LINE 688 "AG.hs" #-}
                   )
              _e2Osyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 693 "AG.hs" #-}
                   )
              ( _e1Iann,_e1Icodes,_e1Ilabels) =
                  e1_ _e1Olabels _e1Osyms 
              ( _e2Iann,_e2Icodes,_e2Ilabels) =
                  e2_ _e2Olabels _e2Osyms 
          in  ( _lhsOann,_lhsOcodes,_lhsOlabels)))
sem_Exp_Eq :: T_Exp  ->
              T_Exp  ->
              T_Exp 
sem_Exp_Eq e1_ e2_  =
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
                  ({-# LINE 130 "./AG/CodeGeneration.ag" #-}
                   _e1Iann ++ "==" ++ _e2Iann
                   {-# LINE 722 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 136 "./AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 727 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 193 "./AG/CodeGeneration.ag" #-}
                   _e1Icodes . _e2Icodes . eq . _annote
                   {-# LINE 732 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 116 "./AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 737 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _e2Ilabels
                   {-# LINE 742 "AG.hs" #-}
                   )
              _e1Olabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 747 "AG.hs" #-}
                   )
              _e1Osyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 752 "AG.hs" #-}
                   )
              _e2Olabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _e1Ilabels
                   {-# LINE 757 "AG.hs" #-}
                   )
              _e2Osyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 762 "AG.hs" #-}
                   )
              ( _e1Iann,_e1Icodes,_e1Ilabels) =
                  e1_ _e1Olabels _e1Osyms 
              ( _e2Iann,_e2Icodes,_e2Ilabels) =
                  e2_ _e2Olabels _e2Osyms 
          in  ( _lhsOann,_lhsOcodes,_lhsOlabels)))
sem_Exp_False_ :: T_Exp 
sem_Exp_False_  =
    (\ _lhsIlabels
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOann :: String
              _lhsOlabels :: ([Label])
              _ann =
                  ({-# LINE 121 "./AG/CodeGeneration.ag" #-}
                   "False"
                   {-# LINE 779 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 136 "./AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 784 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 182 "./AG/CodeGeneration.ag" #-}
                   ldc 0 . _annote
                   {-# LINE 789 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 116 "./AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 794 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 799 "AG.hs" #-}
                   )
          in  ( _lhsOann,_lhsOcodes,_lhsOlabels)))
sem_Exp_Gt :: T_Exp  ->
              T_Exp  ->
              T_Exp 
sem_Exp_Gt e1_ e2_  =
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
                  ({-# LINE 131 "./AG/CodeGeneration.ag" #-}
                   _e1Iann ++ ">"  ++ _e2Iann
                   {-# LINE 824 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 136 "./AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 829 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 194 "./AG/CodeGeneration.ag" #-}
                   _e1Icodes . _e2Icodes . gt . _annote
                   {-# LINE 834 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 116 "./AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 839 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _e2Ilabels
                   {-# LINE 844 "AG.hs" #-}
                   )
              _e1Olabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 849 "AG.hs" #-}
                   )
              _e1Osyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 854 "AG.hs" #-}
                   )
              _e2Olabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _e1Ilabels
                   {-# LINE 859 "AG.hs" #-}
                   )
              _e2Osyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 864 "AG.hs" #-}
                   )
              ( _e1Iann,_e1Icodes,_e1Ilabels) =
                  e1_ _e1Olabels _e1Osyms 
              ( _e2Iann,_e2Icodes,_e2Ilabels) =
                  e2_ _e2Olabels _e2Osyms 
          in  ( _lhsOann,_lhsOcodes,_lhsOlabels)))
sem_Exp_Int :: Int ->
               T_Exp 
sem_Exp_Int n_  =
    (\ _lhsIlabels
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOann :: String
              _lhsOlabels :: ([Label])
              _ann =
                  ({-# LINE 120 "./AG/CodeGeneration.ag" #-}
                   show n_
                   {-# LINE 882 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 136 "./AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 887 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 181 "./AG/CodeGeneration.ag" #-}
                   ldc n_ . _annote
                   {-# LINE 892 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 116 "./AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 897 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 902 "AG.hs" #-}
                   )
          in  ( _lhsOann,_lhsOcodes,_lhsOlabels)))
sem_Exp_Lt :: T_Exp  ->
              T_Exp  ->
              T_Exp 
sem_Exp_Lt e1_ e2_  =
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
                  ({-# LINE 129 "./AG/CodeGeneration.ag" #-}
                   _e1Iann ++ "<"  ++ _e2Iann
                   {-# LINE 927 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 136 "./AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 932 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 192 "./AG/CodeGeneration.ag" #-}
                   _e1Icodes . _e2Icodes . lt . _annote
                   {-# LINE 937 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 116 "./AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 942 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _e2Ilabels
                   {-# LINE 947 "AG.hs" #-}
                   )
              _e1Olabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 952 "AG.hs" #-}
                   )
              _e1Osyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 957 "AG.hs" #-}
                   )
              _e2Olabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _e1Ilabels
                   {-# LINE 962 "AG.hs" #-}
                   )
              _e2Osyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 967 "AG.hs" #-}
                   )
              ( _e1Iann,_e1Icodes,_e1Ilabels) =
                  e1_ _e1Olabels _e1Osyms 
              ( _e2Iann,_e2Icodes,_e2Ilabels) =
                  e2_ _e2Olabels _e2Osyms 
          in  ( _lhsOann,_lhsOcodes,_lhsOlabels)))
sem_Exp_Mul :: T_Exp  ->
               T_Exp  ->
               T_Exp 
sem_Exp_Mul e1_ e2_  =
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
                  ({-# LINE 127 "./AG/CodeGeneration.ag" #-}
                   _e1Iann ++ "*"  ++ _e2Iann
                   {-# LINE 996 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 136 "./AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 1001 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 190 "./AG/CodeGeneration.ag" #-}
                   _e1Icodes . _e2Icodes . mul . _annote
                   {-# LINE 1006 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 116 "./AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 1011 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _e2Ilabels
                   {-# LINE 1016 "AG.hs" #-}
                   )
              _e1Olabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1021 "AG.hs" #-}
                   )
              _e1Osyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1026 "AG.hs" #-}
                   )
              _e2Olabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _e1Ilabels
                   {-# LINE 1031 "AG.hs" #-}
                   )
              _e2Osyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1036 "AG.hs" #-}
                   )
              ( _e1Iann,_e1Icodes,_e1Ilabels) =
                  e1_ _e1Olabels _e1Osyms 
              ( _e2Iann,_e2Icodes,_e2Ilabels) =
                  e2_ _e2Olabels _e2Osyms 
          in  ( _lhsOann,_lhsOcodes,_lhsOlabels)))
sem_Exp_Sub :: T_Exp  ->
               T_Exp  ->
               T_Exp 
sem_Exp_Sub e1_ e2_  =
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
                  ({-# LINE 126 "./AG/CodeGeneration.ag" #-}
                   _e1Iann ++ "-"  ++ _e2Iann
                   {-# LINE 1065 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 136 "./AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 1070 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 189 "./AG/CodeGeneration.ag" #-}
                   _e1Icodes . _e2Icodes . sub . _annote
                   {-# LINE 1075 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 116 "./AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 1080 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _e2Ilabels
                   {-# LINE 1085 "AG.hs" #-}
                   )
              _e1Olabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1090 "AG.hs" #-}
                   )
              _e1Osyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1095 "AG.hs" #-}
                   )
              _e2Olabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _e1Ilabels
                   {-# LINE 1100 "AG.hs" #-}
                   )
              _e2Osyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1105 "AG.hs" #-}
                   )
              ( _e1Iann,_e1Icodes,_e1Ilabels) =
                  e1_ _e1Olabels _e1Osyms 
              ( _e2Iann,_e2Icodes,_e2Ilabels) =
                  e2_ _e2Olabels _e2Osyms 
          in  ( _lhsOann,_lhsOcodes,_lhsOlabels)))
sem_Exp_True_ :: T_Exp 
sem_Exp_True_  =
    (\ _lhsIlabels
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOann :: String
              _lhsOlabels :: ([Label])
              _ann =
                  ({-# LINE 122 "./AG/CodeGeneration.ag" #-}
                   "True"
                   {-# LINE 1122 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 136 "./AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 1127 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 183 "./AG/CodeGeneration.ag" #-}
                   ldc 1 . _annote
                   {-# LINE 1132 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 116 "./AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 1137 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1142 "AG.hs" #-}
                   )
          in  ( _lhsOann,_lhsOcodes,_lhsOlabels)))
sem_Exp_Var :: Ident ->
               T_Exp 
sem_Exp_Var x_  =
    (\ _lhsIlabels
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOann :: String
              _lhsOlabels :: ([Label])
              _ann =
                  ({-# LINE 123 "./AG/CodeGeneration.ag" #-}
                   x_
                   {-# LINE 1156 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 136 "./AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 1161 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 184 "./AG/CodeGeneration.ag" #-}
                   get x_ _lhsIsyms . _annote
                   {-# LINE 1166 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 116 "./AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 1171 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1176 "AG.hs" #-}
                   )
          in  ( _lhsOann,_lhsOcodes,_lhsOlabels)))
-- Exps --------------------------------------------------------
type Exps  = [Exp ]
-- cata
sem_Exps :: Exps  ->
            T_Exps 
sem_Exps list  =
    (Prelude.foldr sem_Exps_Cons sem_Exps_Nil (Prelude.map sem_Exp list) )
-- semantic domain
type T_Exps  = ([Label]) ->
               Syms ->
               ( ([String]),CodeS,([Label]))
data Inh_Exps  = Inh_Exps {labels_Inh_Exps :: ([Label]),syms_Inh_Exps :: Syms}
data Syn_Exps  = Syn_Exps {anns_Syn_Exps :: ([String]),codes_Syn_Exps :: CodeS,labels_Syn_Exps :: ([Label])}
wrap_Exps :: T_Exps  ->
             Inh_Exps  ->
             Syn_Exps 
wrap_Exps sem (Inh_Exps _lhsIlabels _lhsIsyms )  =
    (let ( _lhsOanns,_lhsOcodes,_lhsOlabels) = sem _lhsIlabels _lhsIsyms 
     in  (Syn_Exps _lhsOanns _lhsOcodes _lhsOlabels ))
sem_Exps_Cons :: T_Exp  ->
                 T_Exps  ->
                 T_Exps 
sem_Exps_Cons hd_ tl_  =
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
                  ({-# LINE 134 "./AG/CodeGeneration.ag" #-}
                   _hdIann : _tlIanns
                   {-# LINE 1220 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 143 "./AG/CodeGeneration.ag" #-}
                   _hdIcodes . _tlIcodes
                   {-# LINE 1225 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _tlIlabels
                   {-# LINE 1230 "AG.hs" #-}
                   )
              _hdOlabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1235 "AG.hs" #-}
                   )
              _hdOsyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1240 "AG.hs" #-}
                   )
              _tlOlabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _hdIlabels
                   {-# LINE 1245 "AG.hs" #-}
                   )
              _tlOsyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1250 "AG.hs" #-}
                   )
              ( _hdIann,_hdIcodes,_hdIlabels) =
                  hd_ _hdOlabels _hdOsyms 
              ( _tlIanns,_tlIcodes,_tlIlabels) =
                  tl_ _tlOlabels _tlOsyms 
          in  ( _lhsOanns,_lhsOcodes,_lhsOlabels)))
sem_Exps_Nil :: T_Exps 
sem_Exps_Nil  =
    (\ _lhsIlabels
       _lhsIsyms ->
         (let _lhsOanns :: ([String])
              _lhsOcodes :: CodeS
              _lhsOlabels :: ([Label])
              _lhsOanns =
                  ({-# LINE 133 "./AG/CodeGeneration.ag" #-}
                   []
                   {-# LINE 1267 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 143 "./AG/CodeGeneration.ag" #-}
                   id
                   {-# LINE 1272 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1277 "AG.hs" #-}
                   )
          in  ( _lhsOanns,_lhsOcodes,_lhsOlabels)))
-- Prog --------------------------------------------------------
data Prog  = TopLevelDecls (Decls ) 
-- cata
sem_Prog :: Prog  ->
            T_Prog 
sem_Prog (TopLevelDecls _ds )  =
    (sem_Prog_TopLevelDecls (sem_Decls _ds ) )
-- semantic domain
type T_Prog  = ( Code)
data Inh_Prog  = Inh_Prog {}
data Syn_Prog  = Syn_Prog {code_Syn_Prog :: Code}
wrap_Prog :: T_Prog  ->
             Inh_Prog  ->
             Syn_Prog 
wrap_Prog sem (Inh_Prog )  =
    (let ( _lhsOcode) = sem 
     in  (Syn_Prog _lhsOcode ))
sem_Prog_TopLevelDecls :: T_Decls  ->
                          T_Prog 
sem_Prog_TopLevelDecls ds_  =
    (let _dsOlabels :: ([Label])
         _dsOoffset :: Int
         _dsOsyms :: Syms
         _lhsOcode :: Code
         _dsIcodes :: CodeS
         _dsIenv :: Env
         _dsIlabels :: ([Label])
         _dsIoffset :: Int
         _dsOlabels =
             ({-# LINE 24 "./AG/CodeGeneration.ag" #-}
              [0 ..]
              {-# LINE 1311 "AG.hs" #-}
              )
         _dsOoffset =
             ({-# LINE 45 "./AG/CodeGeneration.ag" #-}
              1
              {-# LINE 1316 "AG.hs" #-}
              )
         _dsOsyms =
             ({-# LINE 106 "./AG/CodeGeneration.ag" #-}
              [_dsIenv]
              {-# LINE 1321 "AG.hs" #-}
              )
         _codes =
             ({-# LINE 145 "./AG/CodeGeneration.ag" #-}
              _dsIcodes .
              enter _dsIenv .
              call "main" [_dsIenv] .
              ajs (- 1) .
              exit _dsIenv
              {-# LINE 1330 "AG.hs" #-}
              )
         _lhsOcode =
             ({-# LINE 199 "./AG/CodeGeneration.ag" #-}
              Code (_codes     [])
              {-# LINE 1335 "AG.hs" #-}
              )
         ( _dsIcodes,_dsIenv,_dsIlabels,_dsIoffset) =
             ds_ _dsOlabels _dsOoffset _dsOsyms 
     in  ( _lhsOcode))
-- Stmt --------------------------------------------------------
data Stmt  = Assign (Ident) (Exp ) 
           | Block (Stmts ) 
           | Call_ (Ident) (Exps ) 
           | Decl (Decl ) 
           | Empty 
           | If (Exp ) (Stmt ) (Stmt ) 
           | Print (Exp ) 
           | Return (Exp ) 
-- cata
sem_Stmt :: Stmt  ->
            T_Stmt 
sem_Stmt (Assign _x _e )  =
    (sem_Stmt_Assign _x (sem_Exp _e ) )
sem_Stmt (Block _b )  =
    (sem_Stmt_Block (sem_Stmts _b ) )
sem_Stmt (Call_ _f _es )  =
    (sem_Stmt_Call_ _f (sem_Exps _es ) )
sem_Stmt (Decl _d )  =
    (sem_Stmt_Decl (sem_Decl _d ) )
sem_Stmt (Empty )  =
    (sem_Stmt_Empty )
sem_Stmt (If _e _s1 _s2 )  =
    (sem_Stmt_If (sem_Exp _e ) (sem_Stmt _s1 ) (sem_Stmt _s2 ) )
sem_Stmt (Print _e )  =
    (sem_Stmt_Print (sem_Exp _e ) )
sem_Stmt (Return _e )  =
    (sem_Stmt_Return (sem_Exp _e ) )
-- semantic domain
type T_Stmt  = ([Label]) ->
               Int ->
               Syms ->
               ( CodeS,Env,([Label]),Int)
data Inh_Stmt  = Inh_Stmt {labels_Inh_Stmt :: ([Label]),offset_Inh_Stmt :: Int,syms_Inh_Stmt :: Syms}
data Syn_Stmt  = Syn_Stmt {codes_Syn_Stmt :: CodeS,env_Syn_Stmt :: Env,labels_Syn_Stmt :: ([Label]),offset_Syn_Stmt :: Int}
wrap_Stmt :: T_Stmt  ->
             Inh_Stmt  ->
             Syn_Stmt 
wrap_Stmt sem (Inh_Stmt _lhsIlabels _lhsIoffset _lhsIsyms )  =
    (let ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset) = sem _lhsIlabels _lhsIoffset _lhsIsyms 
     in  (Syn_Stmt _lhsOcodes _lhsOenv _lhsOlabels _lhsOoffset ))
sem_Stmt_Assign :: Ident ->
                   T_Exp  ->
                   T_Stmt 
sem_Stmt_Assign x_ e_  =
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
                  ({-# LINE 163 "./AG/CodeGeneration.ag" #-}
                   _eIcodes . set x_ _lhsIsyms
                   {-# LINE 1400 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 73 "./AG/CodeGeneration.ag" #-}
                   []
                   {-# LINE 1405 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _eIlabels
                   {-# LINE 1410 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 43 "./AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1415 "AG.hs" #-}
                   )
              _eOlabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1420 "AG.hs" #-}
                   )
              _eOsyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1425 "AG.hs" #-}
                   )
              ( _eIann,_eIcodes,_eIlabels) =
                  e_ _eOlabels _eOsyms 
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset)))
sem_Stmt_Block :: T_Stmts  ->
                  T_Stmt 
sem_Stmt_Block b_  =
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
                  ({-# LINE 48 "./AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1450 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 78 "./AG/CodeGeneration.ag" #-}
                   []
                   {-# LINE 1455 "AG.hs" #-}
                   )
              _bOsyms =
                  ({-# LINE 108 "./AG/CodeGeneration.ag" #-}
                   let local : global = _lhsIsyms
                   in  (local ++ _bIenv) : global
                   {-# LINE 1461 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 177 "./AG/CodeGeneration.ag" #-}
                   enter _bIenv .
                   _bIcodes .
                   exit _bIenv
                   {-# LINE 1468 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _bIlabels
                   {-# LINE 1473 "AG.hs" #-}
                   )
              _bOlabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1478 "AG.hs" #-}
                   )
              _bOoffset =
                  ({-# LINE 42 "./AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1483 "AG.hs" #-}
                   )
              ( _bIcodes,_bIenv,_bIlabels,_bIoffset) =
                  b_ _bOlabels _bOoffset _bOsyms 
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset)))
sem_Stmt_Call_ :: Ident ->
                  T_Exps  ->
                  T_Stmt 
sem_Stmt_Call_ f_ es_  =
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
                  ({-# LINE 164 "./AG/CodeGeneration.ag" #-}
                   wrapSLCacheLoader _lhsIsyms
                    (_esIcodes .
                     call f_ _lhsIsyms) .
                   ajs (- 1)
                   {-# LINE 1510 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 73 "./AG/CodeGeneration.ag" #-}
                   []
                   {-# LINE 1515 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _esIlabels
                   {-# LINE 1520 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 43 "./AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1525 "AG.hs" #-}
                   )
              _esOlabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1530 "AG.hs" #-}
                   )
              _esOsyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1535 "AG.hs" #-}
                   )
              ( _esIanns,_esIcodes,_esIlabels) =
                  es_ _esOlabels _esOsyms 
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset)))
sem_Stmt_Decl :: T_Decl  ->
                 T_Stmt 
sem_Stmt_Decl d_  =
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
                  ({-# LINE 143 "./AG/CodeGeneration.ag" #-}
                   _dIcodes
                   {-# LINE 1560 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 73 "./AG/CodeGeneration.ag" #-}
                   _dIenv
                   {-# LINE 1565 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _dIlabels
                   {-# LINE 1570 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 43 "./AG/CodeGeneration.ag" #-}
                   _dIoffset
                   {-# LINE 1575 "AG.hs" #-}
                   )
              _dOlabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1580 "AG.hs" #-}
                   )
              _dOoffset =
                  ({-# LINE 42 "./AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1585 "AG.hs" #-}
                   )
              _dOsyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1590 "AG.hs" #-}
                   )
              ( _dIcodes,_dIenv,_dIlabels,_dIoffset) =
                  d_ _dOlabels _dOoffset _dOsyms 
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset)))
sem_Stmt_Empty :: T_Stmt 
sem_Stmt_Empty  =
    (\ _lhsIlabels
       _lhsIoffset
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOenv :: Env
              _lhsOlabels :: ([Label])
              _lhsOoffset :: Int
              _lhsOcodes =
                  ({-# LINE 143 "./AG/CodeGeneration.ag" #-}
                   id
                   {-# LINE 1607 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 73 "./AG/CodeGeneration.ag" #-}
                   []
                   {-# LINE 1612 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1617 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 43 "./AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1622 "AG.hs" #-}
                   )
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset)))
sem_Stmt_If :: T_Exp  ->
               T_Stmt  ->
               T_Stmt  ->
               T_Stmt 
sem_Stmt_If e_ s1_ s2_  =
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
                  ({-# LINE 30 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels !! 0
                   {-# LINE 1659 "AG.hs" #-}
                   )
              _fiLabel =
                  ({-# LINE 31 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels !! 1
                   {-# LINE 1664 "AG.hs" #-}
                   )
              _eOlabels =
                  ({-# LINE 32 "./AG/CodeGeneration.ag" #-}
                   drop 2 _lhsIlabels
                   {-# LINE 1669 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 170 "./AG/CodeGeneration.ag" #-}
                   _eIcodes .
                   brf _elseLabel     .
                   _s1Icodes .
                   bra _fiLabel     .
                   label _elseLabel     .
                     _s2Icodes .
                   label _fiLabel
                   {-# LINE 1680 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 73 "./AG/CodeGeneration.ag" #-}
                   _s1Ienv ++ _s2Ienv
                   {-# LINE 1685 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _s2Ilabels
                   {-# LINE 1690 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 43 "./AG/CodeGeneration.ag" #-}
                   _s2Ioffset
                   {-# LINE 1695 "AG.hs" #-}
                   )
              _eOsyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1700 "AG.hs" #-}
                   )
              _s1Olabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _eIlabels
                   {-# LINE 1705 "AG.hs" #-}
                   )
              _s1Ooffset =
                  ({-# LINE 42 "./AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1710 "AG.hs" #-}
                   )
              _s1Osyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1715 "AG.hs" #-}
                   )
              _s2Olabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _s1Ilabels
                   {-# LINE 1720 "AG.hs" #-}
                   )
              _s2Ooffset =
                  ({-# LINE 42 "./AG/CodeGeneration.ag" #-}
                   _s1Ioffset
                   {-# LINE 1725 "AG.hs" #-}
                   )
              _s2Osyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1730 "AG.hs" #-}
                   )
              ( _eIann,_eIcodes,_eIlabels) =
                  e_ _eOlabels _eOsyms 
              ( _s1Icodes,_s1Ienv,_s1Ilabels,_s1Ioffset) =
                  s1_ _s1Olabels _s1Ooffset _s1Osyms 
              ( _s2Icodes,_s2Ienv,_s2Ilabels,_s2Ioffset) =
                  s2_ _s2Olabels _s2Ooffset _s2Osyms 
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset)))
sem_Stmt_Print :: T_Exp  ->
                  T_Stmt 
sem_Stmt_Print e_  =
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
                  ({-# LINE 168 "./AG/CodeGeneration.ag" #-}
                   _eIcodes . trap 0
                   {-# LINE 1757 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 73 "./AG/CodeGeneration.ag" #-}
                   []
                   {-# LINE 1762 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _eIlabels
                   {-# LINE 1767 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 43 "./AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1772 "AG.hs" #-}
                   )
              _eOlabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1777 "AG.hs" #-}
                   )
              _eOsyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1782 "AG.hs" #-}
                   )
              ( _eIann,_eIcodes,_eIlabels) =
                  e_ _eOlabels _eOsyms 
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset)))
sem_Stmt_Return :: T_Exp  ->
                   T_Stmt 
sem_Stmt_Return e_  =
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
                  ({-# LINE 169 "./AG/CodeGeneration.ag" #-}
                   _eIcodes . return_ _lhsIsyms
                   {-# LINE 1805 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 73 "./AG/CodeGeneration.ag" #-}
                   []
                   {-# LINE 1810 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _eIlabels
                   {-# LINE 1815 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 43 "./AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1820 "AG.hs" #-}
                   )
              _eOlabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1825 "AG.hs" #-}
                   )
              _eOsyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1830 "AG.hs" #-}
                   )
              ( _eIann,_eIcodes,_eIlabels) =
                  e_ _eOlabels _eOsyms 
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset)))
-- Stmts -------------------------------------------------------
type Stmts  = [Stmt ]
-- cata
sem_Stmts :: Stmts  ->
             T_Stmts 
sem_Stmts list  =
    (Prelude.foldr sem_Stmts_Cons sem_Stmts_Nil (Prelude.map sem_Stmt list) )
-- semantic domain
type T_Stmts  = ([Label]) ->
                Int ->
                Syms ->
                ( CodeS,Env,([Label]),Int)
data Inh_Stmts  = Inh_Stmts {labels_Inh_Stmts :: ([Label]),offset_Inh_Stmts :: Int,syms_Inh_Stmts :: Syms}
data Syn_Stmts  = Syn_Stmts {codes_Syn_Stmts :: CodeS,env_Syn_Stmts :: Env,labels_Syn_Stmts :: ([Label]),offset_Syn_Stmts :: Int}
wrap_Stmts :: T_Stmts  ->
              Inh_Stmts  ->
              Syn_Stmts 
wrap_Stmts sem (Inh_Stmts _lhsIlabels _lhsIoffset _lhsIsyms )  =
    (let ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset) = sem _lhsIlabels _lhsIoffset _lhsIsyms 
     in  (Syn_Stmts _lhsOcodes _lhsOenv _lhsOlabels _lhsOoffset ))
sem_Stmts_Cons :: T_Stmt  ->
                  T_Stmts  ->
                  T_Stmts 
sem_Stmts_Cons hd_ tl_  =
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
                  ({-# LINE 143 "./AG/CodeGeneration.ag" #-}
                   _hdIcodes . _tlIcodes
                   {-# LINE 1883 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 73 "./AG/CodeGeneration.ag" #-}
                   _hdIenv ++ _tlIenv
                   {-# LINE 1888 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _tlIlabels
                   {-# LINE 1893 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 43 "./AG/CodeGeneration.ag" #-}
                   _tlIoffset
                   {-# LINE 1898 "AG.hs" #-}
                   )
              _hdOlabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1903 "AG.hs" #-}
                   )
              _hdOoffset =
                  ({-# LINE 42 "./AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1908 "AG.hs" #-}
                   )
              _hdOsyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1913 "AG.hs" #-}
                   )
              _tlOlabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _hdIlabels
                   {-# LINE 1918 "AG.hs" #-}
                   )
              _tlOoffset =
                  ({-# LINE 42 "./AG/CodeGeneration.ag" #-}
                   _hdIoffset
                   {-# LINE 1923 "AG.hs" #-}
                   )
              _tlOsyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1928 "AG.hs" #-}
                   )
              ( _hdIcodes,_hdIenv,_hdIlabels,_hdIoffset) =
                  hd_ _hdOlabels _hdOoffset _hdOsyms 
              ( _tlIcodes,_tlIenv,_tlIlabels,_tlIoffset) =
                  tl_ _tlOlabels _tlOoffset _tlOsyms 
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset)))
sem_Stmts_Nil :: T_Stmts 
sem_Stmts_Nil  =
    (\ _lhsIlabels
       _lhsIoffset
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOenv :: Env
              _lhsOlabels :: ([Label])
              _lhsOoffset :: Int
              _lhsOcodes =
                  ({-# LINE 143 "./AG/CodeGeneration.ag" #-}
                   id
                   {-# LINE 1947 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 73 "./AG/CodeGeneration.ag" #-}
                   []
                   {-# LINE 1952 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1957 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 43 "./AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1962 "AG.hs" #-}
                   )
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset)))