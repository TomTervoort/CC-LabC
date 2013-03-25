

-- UUAGC 0.9.38.1 (AG.ag)
module CCO.Imp.AG where

{-# LINE 2 "./AG/CodeGeneration.ag" #-}

import CCO.Ssm hiding (Add, Sub, Mul, Div, Eq, Lt, Gt)
import Prelude hiding (div)
import Data.List (intersperse)

import Debug.Trace
{-# LINE 14 "AG.hs" #-}
{-# LINE 5 "./AG/Base.ag" #-}

type Ident = String    -- ^ Type of identifiers.
{-# LINE 18 "AG.hs" #-}

{-# LINE 50 "./AG/CodeGeneration.ag" #-}

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
{-# LINE 34 "AG.hs" #-}

{-# LINE 85 "./AG/CodeGeneration.ag" #-}

-- | A symbol table contains descriptors for each variable that is in scope at
-- a certain program point.
-- The table consists of levels of 'Env's reflecting the nesting of functions:
-- * The head of the list of 'Env's corresponds to the innermost function scope
--   and so it contains the descriptors of the symbols that are allocated
--   relative to the current mark pointer.
-- * To access the symbols described in the tail of the list, static links are
--   to be followed.
type Syms = [Env]
{-# LINE 47 "AG.hs" #-}

{-# LINE 200 "./AG/CodeGeneration.ag" #-}


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

-- | Produces code for retrieving the value of a variable.
get :: Ident -> Syms -> CodeS
get x (local : global) = case lookup x (vars local) of
  Nothing         -> ldl (- 2) . getGlobal x global
  Just (V offset) -> ldl offset

-- | Produces code for retrieving the value of a global variable.
getGlobal :: Ident -> Syms -> CodeS
getGlobal x []           = error ("unknown variable: " ++ x)
getGlobal x (env : envs) = case lookup x (vars env) of
  Nothing         -> lda (- 2) . getGlobal x envs
  Just (V offset) -> lda offset

-- | Produces code for assigning a new value to a variable.
set :: Ident -> Syms -> CodeS
set x (local : global) = case lookup x (vars local) of
  Nothing         -> ldl (- 2) . setGlobal x global
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
  
-- | Loads the values of the variables neccessary for the static link cache.  
loadSLCache :: Syms -> CodeS
loadSLCache (local : global) = composeList getters
                               . if null getters 
                                  then id
                                  else annote SP (-(length getters) + 1) 0 "red" "SLCache"
 where getters = [get id global | id <- cacheVars local global]

-- | Writes the contents of the static link cache, which should end one above the current SP, back
--   to the corresponding variables. After having popped the cache, the value the SP pointed to 
--   before is restored.
unloadSLCache :: Syms -> CodeS
unloadSLCache (local : global) = ajs (-1)
                                 . composeList setters
                                 . lds (slSize + 1)
                                 . annote SP 0 0 "cyan" "returned"
 where slSize = length (cacheVars local global)
       setters = [set id global | id <- reverse $ cacheVars local global]

cacheVars :: Env -> Syms -> [Ident]
cacheVars local global = concatMap (map (filter isRequired . fst) . vars) global
 where isRequired _ = True

{-# LINE 140 "AG.hs" #-}
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
                  ({-# LINE 22 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels !! 0
                   {-# LINE 186 "AG.hs" #-}
                   )
              _endLabel =
                  ({-# LINE 23 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels !! 1
                   {-# LINE 191 "AG.hs" #-}
                   )
              _bOlabels =
                  ({-# LINE 24 "./AG/CodeGeneration.ag" #-}
                   drop 2 _lhsIlabels
                   {-# LINE 196 "AG.hs" #-}
                   )
              _bOoffset =
                  ({-# LINE 43 "./AG/CodeGeneration.ag" #-}
                   1
                   {-# LINE 201 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 72 "./AG/CodeGeneration.ag" #-}
                   [(f_, F _beginLabel    )]
                   {-# LINE 206 "AG.hs" #-}
                   )
              _params =
                  ({-# LINE 79 "./AG/CodeGeneration.ag" #-}
                   zipWith (\x i -> (x, V i)) xs_ [- (2 + length xs_) ..]
                   {-# LINE 211 "AG.hs" #-}
                   )
              _bOsyms =
                  ({-# LINE 103 "./AG/CodeGeneration.ag" #-}
                   (_params     ++ _bIenv) : _lhsIsyms
                   {-# LINE 216 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 147 "./AG/CodeGeneration.ag" #-}
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
                   {-# LINE 231 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 18 "./AG/CodeGeneration.ag" #-}
                   _bIlabels
                   {-# LINE 236 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 39 "./AG/CodeGeneration.ag" #-}
                   _bIoffset
                   {-# LINE 241 "AG.hs" #-}
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
                  ({-# LINE 42 "./AG/CodeGeneration.ag" #-}
                   _lhsIoffset + 1
                   {-# LINE 259 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 71 "./AG/CodeGeneration.ag" #-}
                   [(x_, V _lhsIoffset    )]
                   {-# LINE 264 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 139 "./AG/CodeGeneration.ag" #-}
                   id
                   {-# LINE 269 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 18 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 274 "AG.hs" #-}
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
                  ({-# LINE 139 "./AG/CodeGeneration.ag" #-}
                   _hdIcodes . _tlIcodes
                   {-# LINE 325 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 69 "./AG/CodeGeneration.ag" #-}
                   _hdIenv ++ _tlIenv
                   {-# LINE 330 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 18 "./AG/CodeGeneration.ag" #-}
                   _tlIlabels
                   {-# LINE 335 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 39 "./AG/CodeGeneration.ag" #-}
                   _tlIoffset
                   {-# LINE 340 "AG.hs" #-}
                   )
              _hdOlabels =
                  ({-# LINE 17 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 345 "AG.hs" #-}
                   )
              _hdOoffset =
                  ({-# LINE 38 "./AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 350 "AG.hs" #-}
                   )
              _hdOsyms =
                  ({-# LINE 100 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 355 "AG.hs" #-}
                   )
              _tlOlabels =
                  ({-# LINE 17 "./AG/CodeGeneration.ag" #-}
                   _hdIlabels
                   {-# LINE 360 "AG.hs" #-}
                   )
              _tlOoffset =
                  ({-# LINE 38 "./AG/CodeGeneration.ag" #-}
                   _hdIoffset
                   {-# LINE 365 "AG.hs" #-}
                   )
              _tlOsyms =
                  ({-# LINE 100 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 370 "AG.hs" #-}
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
                  ({-# LINE 139 "./AG/CodeGeneration.ag" #-}
                   id
                   {-# LINE 389 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 69 "./AG/CodeGeneration.ag" #-}
                   []
                   {-# LINE 394 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 18 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 399 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 39 "./AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 404 "AG.hs" #-}
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
                  ({-# LINE 121 "./AG/CodeGeneration.ag" #-}
                   _e1Iann ++ "+"  ++ _e2Iann
                   {-# LINE 481 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 132 "./AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 486 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 183 "./AG/CodeGeneration.ag" #-}
                   _e1Icodes . _e2Icodes . add . _annote
                   {-# LINE 491 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 112 "./AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 496 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 18 "./AG/CodeGeneration.ag" #-}
                   _e2Ilabels
                   {-# LINE 501 "AG.hs" #-}
                   )
              _e1Olabels =
                  ({-# LINE 17 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 506 "AG.hs" #-}
                   )
              _e1Osyms =
                  ({-# LINE 100 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 511 "AG.hs" #-}
                   )
              _e2Olabels =
                  ({-# LINE 17 "./AG/CodeGeneration.ag" #-}
                   _e1Ilabels
                   {-# LINE 516 "AG.hs" #-}
                   )
              _e2Osyms =
                  ({-# LINE 100 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 521 "AG.hs" #-}
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
                  ({-# LINE 120 "./AG/CodeGeneration.ag" #-}
                   f_ ++ "(" ++ concat (intersperse "," _esIanns) ++ ")"
                   {-# LINE 545 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 132 "./AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 550 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 182 "./AG/CodeGeneration.ag" #-}
                   loadSLCache _lhsIsyms . _esIcodes . call f_ _lhsIsyms . unloadSLCache _lhsIsyms
                   {-# LINE 555 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 112 "./AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 560 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 18 "./AG/CodeGeneration.ag" #-}
                   _esIlabels
                   {-# LINE 565 "AG.hs" #-}
                   )
              _esOlabels =
                  ({-# LINE 17 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 570 "AG.hs" #-}
                   )
              _esOsyms =
                  ({-# LINE 100 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 575 "AG.hs" #-}
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
                  ({-# LINE 124 "./AG/CodeGeneration.ag" #-}
                   _e1Iann ++ "/"  ++ _e2Iann
                   {-# LINE 602 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 132 "./AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 607 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 186 "./AG/CodeGeneration.ag" #-}
                   _e1Icodes . _e2Icodes . div . _annote
                   {-# LINE 612 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 112 "./AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 617 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 18 "./AG/CodeGeneration.ag" #-}
                   _e2Ilabels
                   {-# LINE 622 "AG.hs" #-}
                   )
              _e1Olabels =
                  ({-# LINE 17 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 627 "AG.hs" #-}
                   )
              _e1Osyms =
                  ({-# LINE 100 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 632 "AG.hs" #-}
                   )
              _e2Olabels =
                  ({-# LINE 17 "./AG/CodeGeneration.ag" #-}
                   _e1Ilabels
                   {-# LINE 637 "AG.hs" #-}
                   )
              _e2Osyms =
                  ({-# LINE 100 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 642 "AG.hs" #-}
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
                  ({-# LINE 126 "./AG/CodeGeneration.ag" #-}
                   _e1Iann ++ "==" ++ _e2Iann
                   {-# LINE 671 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 132 "./AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 676 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 188 "./AG/CodeGeneration.ag" #-}
                   _e1Icodes . _e2Icodes . eq . _annote
                   {-# LINE 681 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 112 "./AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 686 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 18 "./AG/CodeGeneration.ag" #-}
                   _e2Ilabels
                   {-# LINE 691 "AG.hs" #-}
                   )
              _e1Olabels =
                  ({-# LINE 17 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 696 "AG.hs" #-}
                   )
              _e1Osyms =
                  ({-# LINE 100 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 701 "AG.hs" #-}
                   )
              _e2Olabels =
                  ({-# LINE 17 "./AG/CodeGeneration.ag" #-}
                   _e1Ilabels
                   {-# LINE 706 "AG.hs" #-}
                   )
              _e2Osyms =
                  ({-# LINE 100 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 711 "AG.hs" #-}
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
                  ({-# LINE 117 "./AG/CodeGeneration.ag" #-}
                   "False"
                   {-# LINE 728 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 132 "./AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 733 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 179 "./AG/CodeGeneration.ag" #-}
                   ldc 0 . _annote
                   {-# LINE 738 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 112 "./AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 743 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 18 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 748 "AG.hs" #-}
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
                  ({-# LINE 127 "./AG/CodeGeneration.ag" #-}
                   _e1Iann ++ ">"  ++ _e2Iann
                   {-# LINE 773 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 132 "./AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 778 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 189 "./AG/CodeGeneration.ag" #-}
                   _e1Icodes . _e2Icodes . gt . _annote
                   {-# LINE 783 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 112 "./AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 788 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 18 "./AG/CodeGeneration.ag" #-}
                   _e2Ilabels
                   {-# LINE 793 "AG.hs" #-}
                   )
              _e1Olabels =
                  ({-# LINE 17 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 798 "AG.hs" #-}
                   )
              _e1Osyms =
                  ({-# LINE 100 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 803 "AG.hs" #-}
                   )
              _e2Olabels =
                  ({-# LINE 17 "./AG/CodeGeneration.ag" #-}
                   _e1Ilabels
                   {-# LINE 808 "AG.hs" #-}
                   )
              _e2Osyms =
                  ({-# LINE 100 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 813 "AG.hs" #-}
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
                  ({-# LINE 116 "./AG/CodeGeneration.ag" #-}
                   show n_
                   {-# LINE 831 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 132 "./AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 836 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 178 "./AG/CodeGeneration.ag" #-}
                   ldc n_ . _annote
                   {-# LINE 841 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 112 "./AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 846 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 18 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 851 "AG.hs" #-}
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
                  ({-# LINE 125 "./AG/CodeGeneration.ag" #-}
                   _e1Iann ++ "<"  ++ _e2Iann
                   {-# LINE 876 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 132 "./AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 881 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 187 "./AG/CodeGeneration.ag" #-}
                   _e1Icodes . _e2Icodes . lt . _annote
                   {-# LINE 886 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 112 "./AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 891 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 18 "./AG/CodeGeneration.ag" #-}
                   _e2Ilabels
                   {-# LINE 896 "AG.hs" #-}
                   )
              _e1Olabels =
                  ({-# LINE 17 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 901 "AG.hs" #-}
                   )
              _e1Osyms =
                  ({-# LINE 100 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 906 "AG.hs" #-}
                   )
              _e2Olabels =
                  ({-# LINE 17 "./AG/CodeGeneration.ag" #-}
                   _e1Ilabels
                   {-# LINE 911 "AG.hs" #-}
                   )
              _e2Osyms =
                  ({-# LINE 100 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 916 "AG.hs" #-}
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
                  ({-# LINE 123 "./AG/CodeGeneration.ag" #-}
                   _e1Iann ++ "*"  ++ _e2Iann
                   {-# LINE 945 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 132 "./AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 950 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 185 "./AG/CodeGeneration.ag" #-}
                   _e1Icodes . _e2Icodes . mul . _annote
                   {-# LINE 955 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 112 "./AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 960 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 18 "./AG/CodeGeneration.ag" #-}
                   _e2Ilabels
                   {-# LINE 965 "AG.hs" #-}
                   )
              _e1Olabels =
                  ({-# LINE 17 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 970 "AG.hs" #-}
                   )
              _e1Osyms =
                  ({-# LINE 100 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 975 "AG.hs" #-}
                   )
              _e2Olabels =
                  ({-# LINE 17 "./AG/CodeGeneration.ag" #-}
                   _e1Ilabels
                   {-# LINE 980 "AG.hs" #-}
                   )
              _e2Osyms =
                  ({-# LINE 100 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 985 "AG.hs" #-}
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
                  ({-# LINE 122 "./AG/CodeGeneration.ag" #-}
                   _e1Iann ++ "-"  ++ _e2Iann
                   {-# LINE 1014 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 132 "./AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 1019 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 184 "./AG/CodeGeneration.ag" #-}
                   _e1Icodes . _e2Icodes . sub . _annote
                   {-# LINE 1024 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 112 "./AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 1029 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 18 "./AG/CodeGeneration.ag" #-}
                   _e2Ilabels
                   {-# LINE 1034 "AG.hs" #-}
                   )
              _e1Olabels =
                  ({-# LINE 17 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1039 "AG.hs" #-}
                   )
              _e1Osyms =
                  ({-# LINE 100 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1044 "AG.hs" #-}
                   )
              _e2Olabels =
                  ({-# LINE 17 "./AG/CodeGeneration.ag" #-}
                   _e1Ilabels
                   {-# LINE 1049 "AG.hs" #-}
                   )
              _e2Osyms =
                  ({-# LINE 100 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1054 "AG.hs" #-}
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
                  ({-# LINE 118 "./AG/CodeGeneration.ag" #-}
                   "True"
                   {-# LINE 1071 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 132 "./AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 1076 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 180 "./AG/CodeGeneration.ag" #-}
                   ldc 1 . _annote
                   {-# LINE 1081 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 112 "./AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 1086 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 18 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1091 "AG.hs" #-}
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
                  ({-# LINE 119 "./AG/CodeGeneration.ag" #-}
                   x_
                   {-# LINE 1105 "AG.hs" #-}
                   )
              _annote =
                  ({-# LINE 132 "./AG/CodeGeneration.ag" #-}
                   annote SP 0 0 "green" _ann
                   {-# LINE 1110 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 181 "./AG/CodeGeneration.ag" #-}
                   get x_ _lhsIsyms . _annote
                   {-# LINE 1115 "AG.hs" #-}
                   )
              _lhsOann =
                  ({-# LINE 112 "./AG/CodeGeneration.ag" #-}
                   _ann
                   {-# LINE 1120 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 18 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1125 "AG.hs" #-}
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
                  ({-# LINE 130 "./AG/CodeGeneration.ag" #-}
                   _hdIann : _tlIanns
                   {-# LINE 1169 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 139 "./AG/CodeGeneration.ag" #-}
                   _hdIcodes . _tlIcodes
                   {-# LINE 1174 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 18 "./AG/CodeGeneration.ag" #-}
                   _tlIlabels
                   {-# LINE 1179 "AG.hs" #-}
                   )
              _hdOlabels =
                  ({-# LINE 17 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1184 "AG.hs" #-}
                   )
              _hdOsyms =
                  ({-# LINE 100 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1189 "AG.hs" #-}
                   )
              _tlOlabels =
                  ({-# LINE 17 "./AG/CodeGeneration.ag" #-}
                   _hdIlabels
                   {-# LINE 1194 "AG.hs" #-}
                   )
              _tlOsyms =
                  ({-# LINE 100 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1199 "AG.hs" #-}
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
                  ({-# LINE 129 "./AG/CodeGeneration.ag" #-}
                   []
                   {-# LINE 1216 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 139 "./AG/CodeGeneration.ag" #-}
                   id
                   {-# LINE 1221 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 18 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1226 "AG.hs" #-}
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
             ({-# LINE 20 "./AG/CodeGeneration.ag" #-}
              [0 ..]
              {-# LINE 1260 "AG.hs" #-}
              )
         _dsOoffset =
             ({-# LINE 41 "./AG/CodeGeneration.ag" #-}
              1
              {-# LINE 1265 "AG.hs" #-}
              )
         _dsOsyms =
             ({-# LINE 102 "./AG/CodeGeneration.ag" #-}
              [_dsIenv]
              {-# LINE 1270 "AG.hs" #-}
              )
         _codes =
             ({-# LINE 141 "./AG/CodeGeneration.ag" #-}
              _dsIcodes .
              enter _dsIenv .
              call "main" [_dsIenv] .
              ajs (- 1) .
              exit _dsIenv
              {-# LINE 1279 "AG.hs" #-}
              )
         _lhsOcode =
             ({-# LINE 194 "./AG/CodeGeneration.ag" #-}
              Code (_codes     [])
              {-# LINE 1284 "AG.hs" #-}
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
                  ({-# LINE 159 "./AG/CodeGeneration.ag" #-}
                   _eIcodes . set x_ _lhsIsyms
                   {-# LINE 1349 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 69 "./AG/CodeGeneration.ag" #-}
                   []
                   {-# LINE 1354 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 18 "./AG/CodeGeneration.ag" #-}
                   _eIlabels
                   {-# LINE 1359 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 39 "./AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1364 "AG.hs" #-}
                   )
              _eOlabels =
                  ({-# LINE 17 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1369 "AG.hs" #-}
                   )
              _eOsyms =
                  ({-# LINE 100 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1374 "AG.hs" #-}
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
                  ({-# LINE 44 "./AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1399 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 74 "./AG/CodeGeneration.ag" #-}
                   []
                   {-# LINE 1404 "AG.hs" #-}
                   )
              _bOsyms =
                  ({-# LINE 104 "./AG/CodeGeneration.ag" #-}
                   let local : global = _lhsIsyms
                   in  (local ++ _bIenv) : global
                   {-# LINE 1410 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 174 "./AG/CodeGeneration.ag" #-}
                   enter _bIenv .
                   _bIcodes .
                   exit _bIenv
                   {-# LINE 1417 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 18 "./AG/CodeGeneration.ag" #-}
                   _bIlabels
                   {-# LINE 1422 "AG.hs" #-}
                   )
              _bOlabels =
                  ({-# LINE 17 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1427 "AG.hs" #-}
                   )
              _bOoffset =
                  ({-# LINE 38 "./AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1432 "AG.hs" #-}
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
                  ({-# LINE 160 "./AG/CodeGeneration.ag" #-}
                   loadSLCache _lhsIsyms .
                   _esIcodes .
                   call f_ _lhsIsyms .
                   unloadSLCache _lhsIsyms .
                   ajs (- 1)
                   {-# LINE 1460 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 69 "./AG/CodeGeneration.ag" #-}
                   []
                   {-# LINE 1465 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 18 "./AG/CodeGeneration.ag" #-}
                   _esIlabels
                   {-# LINE 1470 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 39 "./AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1475 "AG.hs" #-}
                   )
              _esOlabels =
                  ({-# LINE 17 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1480 "AG.hs" #-}
                   )
              _esOsyms =
                  ({-# LINE 100 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1485 "AG.hs" #-}
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
                  ({-# LINE 139 "./AG/CodeGeneration.ag" #-}
                   _dIcodes
                   {-# LINE 1510 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 69 "./AG/CodeGeneration.ag" #-}
                   _dIenv
                   {-# LINE 1515 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 18 "./AG/CodeGeneration.ag" #-}
                   _dIlabels
                   {-# LINE 1520 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 39 "./AG/CodeGeneration.ag" #-}
                   _dIoffset
                   {-# LINE 1525 "AG.hs" #-}
                   )
              _dOlabels =
                  ({-# LINE 17 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1530 "AG.hs" #-}
                   )
              _dOoffset =
                  ({-# LINE 38 "./AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1535 "AG.hs" #-}
                   )
              _dOsyms =
                  ({-# LINE 100 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1540 "AG.hs" #-}
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
                  ({-# LINE 139 "./AG/CodeGeneration.ag" #-}
                   id
                   {-# LINE 1557 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 69 "./AG/CodeGeneration.ag" #-}
                   []
                   {-# LINE 1562 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 18 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1567 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 39 "./AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1572 "AG.hs" #-}
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
                  ({-# LINE 26 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels !! 0
                   {-# LINE 1609 "AG.hs" #-}
                   )
              _fiLabel =
                  ({-# LINE 27 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels !! 1
                   {-# LINE 1614 "AG.hs" #-}
                   )
              _eOlabels =
                  ({-# LINE 28 "./AG/CodeGeneration.ag" #-}
                   drop 2 _lhsIlabels
                   {-# LINE 1619 "AG.hs" #-}
                   )
              _lhsOcodes =
                  ({-# LINE 167 "./AG/CodeGeneration.ag" #-}
                   _eIcodes .
                   brf _elseLabel     .
                   _s1Icodes .
                   bra _fiLabel     .
                   label _elseLabel     .
                     _s2Icodes .
                   label _fiLabel
                   {-# LINE 1630 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 69 "./AG/CodeGeneration.ag" #-}
                   _s1Ienv ++ _s2Ienv
                   {-# LINE 1635 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 18 "./AG/CodeGeneration.ag" #-}
                   _s2Ilabels
                   {-# LINE 1640 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 39 "./AG/CodeGeneration.ag" #-}
                   _s2Ioffset
                   {-# LINE 1645 "AG.hs" #-}
                   )
              _eOsyms =
                  ({-# LINE 100 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1650 "AG.hs" #-}
                   )
              _s1Olabels =
                  ({-# LINE 17 "./AG/CodeGeneration.ag" #-}
                   _eIlabels
                   {-# LINE 1655 "AG.hs" #-}
                   )
              _s1Ooffset =
                  ({-# LINE 38 "./AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1660 "AG.hs" #-}
                   )
              _s1Osyms =
                  ({-# LINE 100 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1665 "AG.hs" #-}
                   )
              _s2Olabels =
                  ({-# LINE 17 "./AG/CodeGeneration.ag" #-}
                   _s1Ilabels
                   {-# LINE 1670 "AG.hs" #-}
                   )
              _s2Ooffset =
                  ({-# LINE 38 "./AG/CodeGeneration.ag" #-}
                   _s1Ioffset
                   {-# LINE 1675 "AG.hs" #-}
                   )
              _s2Osyms =
                  ({-# LINE 100 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1680 "AG.hs" #-}
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
                  ({-# LINE 165 "./AG/CodeGeneration.ag" #-}
                   _eIcodes . trap 0
                   {-# LINE 1707 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 69 "./AG/CodeGeneration.ag" #-}
                   []
                   {-# LINE 1712 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 18 "./AG/CodeGeneration.ag" #-}
                   _eIlabels
                   {-# LINE 1717 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 39 "./AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1722 "AG.hs" #-}
                   )
              _eOlabels =
                  ({-# LINE 17 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1727 "AG.hs" #-}
                   )
              _eOsyms =
                  ({-# LINE 100 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1732 "AG.hs" #-}
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
                  ({-# LINE 166 "./AG/CodeGeneration.ag" #-}
                   _eIcodes . return_ _lhsIsyms
                   {-# LINE 1755 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 69 "./AG/CodeGeneration.ag" #-}
                   []
                   {-# LINE 1760 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 18 "./AG/CodeGeneration.ag" #-}
                   _eIlabels
                   {-# LINE 1765 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 39 "./AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1770 "AG.hs" #-}
                   )
              _eOlabels =
                  ({-# LINE 17 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1775 "AG.hs" #-}
                   )
              _eOsyms =
                  ({-# LINE 100 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1780 "AG.hs" #-}
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
                  ({-# LINE 139 "./AG/CodeGeneration.ag" #-}
                   _hdIcodes . _tlIcodes
                   {-# LINE 1833 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 69 "./AG/CodeGeneration.ag" #-}
                   _hdIenv ++ _tlIenv
                   {-# LINE 1838 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 18 "./AG/CodeGeneration.ag" #-}
                   _tlIlabels
                   {-# LINE 1843 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 39 "./AG/CodeGeneration.ag" #-}
                   _tlIoffset
                   {-# LINE 1848 "AG.hs" #-}
                   )
              _hdOlabels =
                  ({-# LINE 17 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1853 "AG.hs" #-}
                   )
              _hdOoffset =
                  ({-# LINE 38 "./AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1858 "AG.hs" #-}
                   )
              _hdOsyms =
                  ({-# LINE 100 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1863 "AG.hs" #-}
                   )
              _tlOlabels =
                  ({-# LINE 17 "./AG/CodeGeneration.ag" #-}
                   _hdIlabels
                   {-# LINE 1868 "AG.hs" #-}
                   )
              _tlOoffset =
                  ({-# LINE 38 "./AG/CodeGeneration.ag" #-}
                   _hdIoffset
                   {-# LINE 1873 "AG.hs" #-}
                   )
              _tlOsyms =
                  ({-# LINE 100 "./AG/CodeGeneration.ag" #-}
                   _lhsIsyms
                   {-# LINE 1878 "AG.hs" #-}
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
                  ({-# LINE 139 "./AG/CodeGeneration.ag" #-}
                   id
                   {-# LINE 1897 "AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 69 "./AG/CodeGeneration.ag" #-}
                   []
                   {-# LINE 1902 "AG.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 18 "./AG/CodeGeneration.ag" #-}
                   _lhsIlabels
                   {-# LINE 1907 "AG.hs" #-}
                   )
              _lhsOoffset =
                  ({-# LINE 39 "./AG/CodeGeneration.ag" #-}
                   _lhsIoffset
                   {-# LINE 1912 "AG.hs" #-}
                   )
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset)))