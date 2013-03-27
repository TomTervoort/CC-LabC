

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
  Nothing         -> getCached x (local:global)
  Just (V offset) -> ldl offset

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
  Nothing         -> setCached x (local:global)
  Just (V offset) -> stl offset

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

{-# LINE 175 "AG.hs" #-}
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
                   {-# LINE 221 "AG.hs" #-}
                   )
              _endLabel =
                  ({-# LINE 27 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels !! 1
                   {-# LINE 226 "AG.hs" #-}
                   )
              _bOlabels =
                  ({-# LINE 28 "./AG/CodeGeneration.ag" #-}
                   drop 2 _lhsIlabels
                   {-# LINE 231 "AG.hs" #-}
                   )
              _bOoffset =
                  ({-# LINE 47 "./AG/CodeGeneration.ag" #-}
                   1
                   {-# LINE 236 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 76 "./AG/CodeGeneration.ag" #-}
                   [(f_, F _beginLabel    )]
                   {-# LINE 241 "AG.hs" #-}
                   )
              _params =
                  ({-# LINE 83 "./AG/CodeGeneration.ag" #-}
                   zipWith (\x i -> (x, V i)) xs_ [- (2 + length xs_) ..]
                   {-# LINE 246 "AG.hs" #-}
                   )
              _bOsyms =
                  ({-# LINE 107 "./AG/CodeGeneration.ag" #-}
                   (_params     ++ _bIenv) : _lhsIsyms
                   {-# LINE 251 "AG.hs" #-}
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
                   {-# LINE 266 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _bIlabels
                   {-# LINE 271 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 43 "./AG/CodeGeneration.ag" #-}
                   _bIoffset
                   {-# LINE 276 "AG.hs" #-}
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
                   {-# LINE 294 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 75 "./AG/CodeGeneration.ag" #-}
                   [(x_, V _lhsIoffset    )]
                   {-# LINE 299 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 143 "./AG/CodeGeneration.ag" #-}
                   id
                   {-# LINE 304 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 309 "AG.hs" #-}
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
                   {-# LINE 360 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 73 "./AG/CodeGeneration.ag" #-}
                   _hdIenv ++ _tlIenv
                   {-# LINE 365 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _tlIlabels
                   {-# LINE 370 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 43 "./AG/CodeGeneration.ag" #-}
                   _tlIoffset
                   {-# LINE 375 "AG.hs" #-}
                   )
              _hdOlabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 380 "AG.hs" #-}
                   )
              _hdOoffset =
                  ({-# LINE 42 "./AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 385 "AG.hs" #-}
                   )
              _hdOsyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 390 "AG.hs" #-}
                   )
              _tlOlabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _hdIlabels
                   {-# LINE 395 "AG.hs" #-}
                   )
              _tlOoffset =
                  ({-# LINE 42 "./AG/CodeGeneration.ag" #-}
                   _hdIoffset
                   {-# LINE 400 "AG.hs" #-}
                   )
              _tlOsyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 405 "AG.hs" #-}
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
                   {-# LINE 424 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 73 "./AG/CodeGeneration.ag" #-}
                   []
                   {-# LINE 429 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 434 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 43 "./AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 439 "AG.hs" #-}
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
                   {-# LINE 516 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 136 "./AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 521 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 188 "./AG/CodeGeneration.ag" #-}
                   _e1Icodes . _e2Icodes . add . _annote
                   {-# LINE 526 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 116 "./AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 531 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _e2Ilabels
                   {-# LINE 536 "AG.hs" #-}
                   )
              _e1Olabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 541 "AG.hs" #-}
                   )
              _e1Osyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 546 "AG.hs" #-}
                   )
              _e2Olabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _e1Ilabels
                   {-# LINE 551 "AG.hs" #-}
                   )
              _e2Osyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 556 "AG.hs" #-}
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
                   {-# LINE 580 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 136 "./AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 585 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 185 "./AG/CodeGeneration.ag" #-}
                   wrapSLCacheLoader _lhsIsyms
                    (_esIcodes .
                     call f_ _lhsIsyms)
                   {-# LINE 592 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 116 "./AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 597 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _esIlabels
                   {-# LINE 602 "AG.hs" #-}
                   )
              _esOlabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 607 "AG.hs" #-}
                   )
              _esOsyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 612 "AG.hs" #-}
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
                   {-# LINE 639 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 136 "./AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 644 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 191 "./AG/CodeGeneration.ag" #-}
                   _e1Icodes . _e2Icodes . div . _annote
                   {-# LINE 649 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 116 "./AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 654 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _e2Ilabels
                   {-# LINE 659 "AG.hs" #-}
                   )
              _e1Olabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 664 "AG.hs" #-}
                   )
              _e1Osyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 669 "AG.hs" #-}
                   )
              _e2Olabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _e1Ilabels
                   {-# LINE 674 "AG.hs" #-}
                   )
              _e2Osyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 679 "AG.hs" #-}
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
                   {-# LINE 708 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 136 "./AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 713 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 193 "./AG/CodeGeneration.ag" #-}
                   _e1Icodes . _e2Icodes . eq . _annote
                   {-# LINE 718 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 116 "./AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 723 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _e2Ilabels
                   {-# LINE 728 "AG.hs" #-}
                   )
              _e1Olabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 733 "AG.hs" #-}
                   )
              _e1Osyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 738 "AG.hs" #-}
                   )
              _e2Olabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _e1Ilabels
                   {-# LINE 743 "AG.hs" #-}
                   )
              _e2Osyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 748 "AG.hs" #-}
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
                   {-# LINE 765 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 136 "./AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 770 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 182 "./AG/CodeGeneration.ag" #-}
                   ldc 0 . _annote
                   {-# LINE 775 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 116 "./AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 780 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 785 "AG.hs" #-}
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
                   {-# LINE 810 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 136 "./AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 815 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 194 "./AG/CodeGeneration.ag" #-}
                   _e1Icodes . _e2Icodes . gt . _annote
                   {-# LINE 820 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 116 "./AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 825 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _e2Ilabels
                   {-# LINE 830 "AG.hs" #-}
                   )
              _e1Olabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 835 "AG.hs" #-}
                   )
              _e1Osyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 840 "AG.hs" #-}
                   )
              _e2Olabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _e1Ilabels
                   {-# LINE 845 "AG.hs" #-}
                   )
              _e2Osyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 850 "AG.hs" #-}
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
                   {-# LINE 868 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 136 "./AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 873 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 181 "./AG/CodeGeneration.ag" #-}
                   ldc n_ . _annote
                   {-# LINE 878 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 116 "./AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 883 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 888 "AG.hs" #-}
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
                   {-# LINE 913 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 136 "./AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 918 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 192 "./AG/CodeGeneration.ag" #-}
                   _e1Icodes . _e2Icodes . lt . _annote
                   {-# LINE 923 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 116 "./AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 928 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _e2Ilabels
                   {-# LINE 933 "AG.hs" #-}
                   )
              _e1Olabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 938 "AG.hs" #-}
                   )
              _e1Osyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 943 "AG.hs" #-}
                   )
              _e2Olabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _e1Ilabels
                   {-# LINE 948 "AG.hs" #-}
                   )
              _e2Osyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 953 "AG.hs" #-}
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
                   {-# LINE 982 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 136 "./AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 987 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 190 "./AG/CodeGeneration.ag" #-}
                   _e1Icodes . _e2Icodes . mul . _annote
                   {-# LINE 992 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 116 "./AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 997 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _e2Ilabels
                   {-# LINE 1002 "AG.hs" #-}
                   )
              _e1Olabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1007 "AG.hs" #-}
                   )
              _e1Osyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1012 "AG.hs" #-}
                   )
              _e2Olabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _e1Ilabels
                   {-# LINE 1017 "AG.hs" #-}
                   )
              _e2Osyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1022 "AG.hs" #-}
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
                   {-# LINE 1051 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 136 "./AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 1056 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 189 "./AG/CodeGeneration.ag" #-}
                   _e1Icodes . _e2Icodes . sub . _annote
                   {-# LINE 1061 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 116 "./AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 1066 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _e2Ilabels
                   {-# LINE 1071 "AG.hs" #-}
                   )
              _e1Olabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1076 "AG.hs" #-}
                   )
              _e1Osyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1081 "AG.hs" #-}
                   )
              _e2Olabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _e1Ilabels
                   {-# LINE 1086 "AG.hs" #-}
                   )
              _e2Osyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1091 "AG.hs" #-}
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
                   {-# LINE 1108 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 136 "./AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 1113 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 183 "./AG/CodeGeneration.ag" #-}
                   ldc 1 . _annote
                   {-# LINE 1118 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 116 "./AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 1123 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1128 "AG.hs" #-}
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
                   {-# LINE 1142 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 136 "./AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 1147 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 184 "./AG/CodeGeneration.ag" #-}
                   get x_ _lhsIsyms . _annote
                   {-# LINE 1152 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 116 "./AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 1157 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1162 "AG.hs" #-}
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
                   {-# LINE 1206 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 143 "./AG/CodeGeneration.ag" #-}
                   _hdIcodes . _tlIcodes
                   {-# LINE 1211 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _tlIlabels
                   {-# LINE 1216 "AG.hs" #-}
                   )
              _hdOlabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1221 "AG.hs" #-}
                   )
              _hdOsyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1226 "AG.hs" #-}
                   )
              _tlOlabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _hdIlabels
                   {-# LINE 1231 "AG.hs" #-}
                   )
              _tlOsyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1236 "AG.hs" #-}
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
                   {-# LINE 1253 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 143 "./AG/CodeGeneration.ag" #-}
                   id
                   {-# LINE 1258 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1263 "AG.hs" #-}
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
              {-# LINE 1297 "AG.hs" #-}
              )
         _dsOoffset =
             ({-# LINE 45 "./AG/CodeGeneration.ag" #-}
              1
              {-# LINE 1302 "AG.hs" #-}
              )
         _dsOsyms =
             ({-# LINE 106 "./AG/CodeGeneration.ag" #-}
              [_dsIenv]
              {-# LINE 1307 "AG.hs" #-}
              )
         _codes =
             ({-# LINE 145 "./AG/CodeGeneration.ag" #-}
              _dsIcodes .
              enter _dsIenv .
              call "main" [_dsIenv] .
              ajs (- 1) .
              exit _dsIenv
              {-# LINE 1316 "AG.hs" #-}
              )
         _lhsOcode =
             ({-# LINE 199 "./AG/CodeGeneration.ag" #-}
              Code (_codes     [])
              {-# LINE 1321 "AG.hs" #-}
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
                   {-# LINE 1386 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 73 "./AG/CodeGeneration.ag" #-}
                   []
                   {-# LINE 1391 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _eIlabels
                   {-# LINE 1396 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 43 "./AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1401 "AG.hs" #-}
                   )
              _eOlabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1406 "AG.hs" #-}
                   )
              _eOsyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1411 "AG.hs" #-}
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
                   {-# LINE 1436 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 78 "./AG/CodeGeneration.ag" #-}
                   []
                   {-# LINE 1441 "AG.hs" #-}
                   )
              _bOsyms =
                  ({-# LINE 108 "./AG/CodeGeneration.ag" #-}
                   let local : global = _lhsIsyms
                   in  (local ++ _bIenv) : global
                   {-# LINE 1447 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 177 "./AG/CodeGeneration.ag" #-}
                   enter _bIenv .
                   _bIcodes .
                   exit _bIenv
                   {-# LINE 1454 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _bIlabels
                   {-# LINE 1459 "AG.hs" #-}
                   )
              _bOlabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1464 "AG.hs" #-}
                   )
              _bOoffset =
                  ({-# LINE 42 "./AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1469 "AG.hs" #-}
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
                   {-# LINE 1496 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 73 "./AG/CodeGeneration.ag" #-}
                   []
                   {-# LINE 1501 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _esIlabels
                   {-# LINE 1506 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 43 "./AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1511 "AG.hs" #-}
                   )
              _esOlabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1516 "AG.hs" #-}
                   )
              _esOsyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1521 "AG.hs" #-}
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
                   {-# LINE 1546 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 73 "./AG/CodeGeneration.ag" #-}
                   _dIenv
                   {-# LINE 1551 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _dIlabels
                   {-# LINE 1556 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 43 "./AG/CodeGeneration.ag" #-}
                   _dIoffset
                   {-# LINE 1561 "AG.hs" #-}
                   )
              _dOlabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1566 "AG.hs" #-}
                   )
              _dOoffset =
                  ({-# LINE 42 "./AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1571 "AG.hs" #-}
                   )
              _dOsyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1576 "AG.hs" #-}
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
                   {-# LINE 1593 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 73 "./AG/CodeGeneration.ag" #-}
                   []
                   {-# LINE 1598 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1603 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 43 "./AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1608 "AG.hs" #-}
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
                   {-# LINE 1645 "AG.hs" #-}
                   )
              _fiLabel =
                  ({-# LINE 31 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels !! 1
                   {-# LINE 1650 "AG.hs" #-}
                   )
              _eOlabels =
                  ({-# LINE 32 "./AG/CodeGeneration.ag" #-}
                   drop 2 _lhsIlabels
                   {-# LINE 1655 "AG.hs" #-}
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
                   {-# LINE 1666 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 73 "./AG/CodeGeneration.ag" #-}
                   _s1Ienv ++ _s2Ienv
                   {-# LINE 1671 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _s2Ilabels
                   {-# LINE 1676 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 43 "./AG/CodeGeneration.ag" #-}
                   _s2Ioffset
                   {-# LINE 1681 "AG.hs" #-}
                   )
              _eOsyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1686 "AG.hs" #-}
                   )
              _s1Olabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _eIlabels
                   {-# LINE 1691 "AG.hs" #-}
                   )
              _s1Ooffset =
                  ({-# LINE 42 "./AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1696 "AG.hs" #-}
                   )
              _s1Osyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1701 "AG.hs" #-}
                   )
              _s2Olabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _s1Ilabels
                   {-# LINE 1706 "AG.hs" #-}
                   )
              _s2Ooffset =
                  ({-# LINE 42 "./AG/CodeGeneration.ag" #-}
                   _s1Ioffset
                   {-# LINE 1711 "AG.hs" #-}
                   )
              _s2Osyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1716 "AG.hs" #-}
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
                   {-# LINE 1743 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 73 "./AG/CodeGeneration.ag" #-}
                   []
                   {-# LINE 1748 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _eIlabels
                   {-# LINE 1753 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 43 "./AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1758 "AG.hs" #-}
                   )
              _eOlabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1763 "AG.hs" #-}
                   )
              _eOsyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1768 "AG.hs" #-}
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
                   {-# LINE 1791 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 73 "./AG/CodeGeneration.ag" #-}
                   []
                   {-# LINE 1796 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _eIlabels
                   {-# LINE 1801 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 43 "./AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1806 "AG.hs" #-}
                   )
              _eOlabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1811 "AG.hs" #-}
                   )
              _eOsyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1816 "AG.hs" #-}
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
                   {-# LINE 1869 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 73 "./AG/CodeGeneration.ag" #-}
                   _hdIenv ++ _tlIenv
                   {-# LINE 1874 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _tlIlabels
                   {-# LINE 1879 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 43 "./AG/CodeGeneration.ag" #-}
                   _tlIoffset
                   {-# LINE 1884 "AG.hs" #-}
                   )
              _hdOlabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1889 "AG.hs" #-}
                   )
              _hdOoffset =
                  ({-# LINE 42 "./AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1894 "AG.hs" #-}
                   )
              _hdOsyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1899 "AG.hs" #-}
                   )
              _tlOlabels =
                  ({-# LINE 21 "./AG/CodeGeneration.ag" #-}
                   _hdIlabels
                   {-# LINE 1904 "AG.hs" #-}
                   )
              _tlOoffset =
                  ({-# LINE 42 "./AG/CodeGeneration.ag" #-}
                   _hdIoffset
                   {-# LINE 1909 "AG.hs" #-}
                   )
              _tlOsyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1914 "AG.hs" #-}
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
                   {-# LINE 1933 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 73 "./AG/CodeGeneration.ag" #-}
                   []
                   {-# LINE 1938 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1943 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 43 "./AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1948 "AG.hs" #-}
                   )
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset)))