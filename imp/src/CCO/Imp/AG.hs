

-- UUAGC 0.9.10 (src/CCO/Imp/AG.ag)
module CCO.Imp.AG where

{-# LINE 2 "src/CCO/Imp/AG/CodeGeneration.ag" #-}

import CCO.Ssm hiding (Add, Sub, Mul, Div, Eq, Lt, Gt)
import Prelude hiding (div)
import Data.List (intersperse)
{-# LINE 12 "src/CCO/Imp/AG.hs" #-}
{-# LINE 5 "src/CCO/Imp/AG/Base.ag" #-}

type Ident = String    -- ^ Type of identifiers.
{-# LINE 16 "src/CCO/Imp/AG.hs" #-}

{-# LINE 48 "src/CCO/Imp/AG/CodeGeneration.ag" #-}

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
{-# LINE 32 "src/CCO/Imp/AG.hs" #-}

{-# LINE 83 "src/CCO/Imp/AG/CodeGeneration.ag" #-}

-- | A symbol table contains descriptors for each variable that is in scope at
-- a certain program point.
-- The table consists of levels of 'Env's reflecting the nesting of functions:
-- * The head of the list of 'Env's corresponds to the innermost function scope
--   and so it contains the descriptors of the symbols that are allocated
--   relative to the current mark pointer.
-- * To access the symbols described in the tail of the list, static links are
--   to be followed.
type Syms = [Env]
{-# LINE 45 "src/CCO/Imp/AG.hs" #-}

{-# LINE 196 "src/CCO/Imp/AG/CodeGeneration.ag" #-}

-- | Produces code for annotating parameters.
enterparams :: Env -> CodeS
enterparams env = foldr (.) id [annote MP off off "green" (x ++ " (param)") | (x, V off) <- env]

-- | Produces code for entering a block.
enter :: Env -> CodeS
enter env = foldr (.) id [ldc 0 . annote SP 0 0 "green" (x ++ " (var)") | (x, V _) <- env]

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
return_ (local : _) =
  sts (- (length (vars local) + 3)) .
  ldrr SP MP .
  str MP .
  sts (- length (params local)) .
  ajs (- (length (params local) - 1)) .
  ret
{-# LINE 109 "src/CCO/Imp/AG.hs" #-}
-- Decl --------------------------------------------------------
data Decl  = FunDecl (Ident) ([Ident]) (Stmts) 
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
               ( CodeS,Env,([Label]),Int,Decl)
data Inh_Decl  = Inh_Decl {labels_Inh_Decl :: [Label],offset_Inh_Decl :: Int,syms_Inh_Decl :: Syms}
data Syn_Decl  = Syn_Decl {codes_Syn_Decl :: CodeS,env_Syn_Decl :: Env,labels_Syn_Decl :: [Label],offset_Syn_Decl :: Int,self_Syn_Decl :: Decl}
wrap_Decl :: T_Decl  ->
             Inh_Decl  ->
             Syn_Decl 
wrap_Decl sem (Inh_Decl _lhsIlabels _lhsIoffset _lhsIsyms )  =
    (let ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset,_lhsOself) =
             (sem _lhsIlabels _lhsIoffset _lhsIsyms )
     in  (Syn_Decl _lhsOcodes _lhsOenv _lhsOlabels _lhsOoffset _lhsOself ))
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
              _lhsOself :: Decl
              _lhsOlabels :: ([Label])
              _lhsOoffset :: Int
              _bIcodes :: CodeS
              _bIenv :: Env
              _bIlabels :: ([Label])
              _bIoffset :: Int
              _bIself :: Stmts
              _beginLabel =
                  {-# LINE 20 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIlabels !! 0
                  {-# LINE 158 "src/CCO/Imp/AG.hs" #-}
              _endLabel =
                  {-# LINE 21 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIlabels !! 1
                  {-# LINE 162 "src/CCO/Imp/AG.hs" #-}
              _bOlabels =
                  {-# LINE 22 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  drop 2 _lhsIlabels
                  {-# LINE 166 "src/CCO/Imp/AG.hs" #-}
              _bOoffset =
                  {-# LINE 41 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  1
                  {-# LINE 170 "src/CCO/Imp/AG.hs" #-}
              _lhsOenv =
                  {-# LINE 70 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  [(f_, F _beginLabel    )]
                  {-# LINE 174 "src/CCO/Imp/AG.hs" #-}
              _params =
                  {-# LINE 77 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  zipWith (\x i -> (x, V i)) xs_ [- (2 + length xs_) ..]
                  {-# LINE 178 "src/CCO/Imp/AG.hs" #-}
              _bOsyms =
                  {-# LINE 101 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  (_params     ++ _bIenv) : _lhsIsyms
                  {-# LINE 182 "src/CCO/Imp/AG.hs" #-}
              _lhsOcodes =
                  {-# LINE 145 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
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
                  {-# LINE 196 "src/CCO/Imp/AG.hs" #-}
              _self =
                  FunDecl f_ xs_ _bIself
              _lhsOself =
                  _self
              _lhsOlabels =
                  {-# LINE 16 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _bIlabels
                  {-# LINE 204 "src/CCO/Imp/AG.hs" #-}
              _lhsOoffset =
                  {-# LINE 37 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _bIoffset
                  {-# LINE 208 "src/CCO/Imp/AG.hs" #-}
              ( _bIcodes,_bIenv,_bIlabels,_bIoffset,_bIself) =
                  (b_ _bOlabels _bOoffset _bOsyms )
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset,_lhsOself)))
sem_Decl_VarDecl :: Ident ->
                    T_Decl 
sem_Decl_VarDecl x_  =
    (\ _lhsIlabels
       _lhsIoffset
       _lhsIsyms ->
         (let _lhsOoffset :: Int
              _lhsOenv :: Env
              _lhsOcodes :: CodeS
              _lhsOself :: Decl
              _lhsOlabels :: ([Label])
              _lhsOoffset =
                  {-# LINE 40 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIoffset + 1
                  {-# LINE 226 "src/CCO/Imp/AG.hs" #-}
              _lhsOenv =
                  {-# LINE 69 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  [(x_, V _lhsIoffset    )]
                  {-# LINE 230 "src/CCO/Imp/AG.hs" #-}
              _lhsOcodes =
                  {-# LINE 137 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  id
                  {-# LINE 234 "src/CCO/Imp/AG.hs" #-}
              _self =
                  VarDecl x_
              _lhsOself =
                  _self
              _lhsOlabels =
                  {-# LINE 16 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIlabels
                  {-# LINE 242 "src/CCO/Imp/AG.hs" #-}
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset,_lhsOself)))
-- Decls -------------------------------------------------------
type Decls  = [(Decl)]
-- cata
sem_Decls :: Decls  ->
             T_Decls 
sem_Decls list  =
    (Prelude.foldr sem_Decls_Cons sem_Decls_Nil (Prelude.map sem_Decl list) )
-- semantic domain
type T_Decls  = ([Label]) ->
                Int ->
                Syms ->
                ( CodeS,Env,([Label]),Int,Decls)
data Inh_Decls  = Inh_Decls {labels_Inh_Decls :: [Label],offset_Inh_Decls :: Int,syms_Inh_Decls :: Syms}
data Syn_Decls  = Syn_Decls {codes_Syn_Decls :: CodeS,env_Syn_Decls :: Env,labels_Syn_Decls :: [Label],offset_Syn_Decls :: Int,self_Syn_Decls :: Decls}
wrap_Decls :: T_Decls  ->
              Inh_Decls  ->
              Syn_Decls 
wrap_Decls sem (Inh_Decls _lhsIlabels _lhsIoffset _lhsIsyms )  =
    (let ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset,_lhsOself) =
             (sem _lhsIlabels _lhsIoffset _lhsIsyms )
     in  (Syn_Decls _lhsOcodes _lhsOenv _lhsOlabels _lhsOoffset _lhsOself ))
sem_Decls_Cons :: T_Decl  ->
                  T_Decls  ->
                  T_Decls 
sem_Decls_Cons hd_ tl_  =
    (\ _lhsIlabels
       _lhsIoffset
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOenv :: Env
              _lhsOself :: Decls
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
              _hdIself :: Decl
              _tlIcodes :: CodeS
              _tlIenv :: Env
              _tlIlabels :: ([Label])
              _tlIoffset :: Int
              _tlIself :: Decls
              _lhsOcodes =
                  {-# LINE 137 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _hdIcodes . _tlIcodes
                  {-# LINE 296 "src/CCO/Imp/AG.hs" #-}
              _lhsOenv =
                  {-# LINE 67 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _hdIenv ++ _tlIenv
                  {-# LINE 300 "src/CCO/Imp/AG.hs" #-}
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOlabels =
                  {-# LINE 16 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _tlIlabels
                  {-# LINE 308 "src/CCO/Imp/AG.hs" #-}
              _lhsOoffset =
                  {-# LINE 37 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _tlIoffset
                  {-# LINE 312 "src/CCO/Imp/AG.hs" #-}
              _hdOlabels =
                  {-# LINE 15 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIlabels
                  {-# LINE 316 "src/CCO/Imp/AG.hs" #-}
              _hdOoffset =
                  {-# LINE 36 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIoffset
                  {-# LINE 320 "src/CCO/Imp/AG.hs" #-}
              _hdOsyms =
                  {-# LINE 98 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIsyms
                  {-# LINE 324 "src/CCO/Imp/AG.hs" #-}
              _tlOlabels =
                  {-# LINE 15 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _hdIlabels
                  {-# LINE 328 "src/CCO/Imp/AG.hs" #-}
              _tlOoffset =
                  {-# LINE 36 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _hdIoffset
                  {-# LINE 332 "src/CCO/Imp/AG.hs" #-}
              _tlOsyms =
                  {-# LINE 98 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIsyms
                  {-# LINE 336 "src/CCO/Imp/AG.hs" #-}
              ( _hdIcodes,_hdIenv,_hdIlabels,_hdIoffset,_hdIself) =
                  (hd_ _hdOlabels _hdOoffset _hdOsyms )
              ( _tlIcodes,_tlIenv,_tlIlabels,_tlIoffset,_tlIself) =
                  (tl_ _tlOlabels _tlOoffset _tlOsyms )
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset,_lhsOself)))
sem_Decls_Nil :: T_Decls 
sem_Decls_Nil  =
    (\ _lhsIlabels
       _lhsIoffset
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOenv :: Env
              _lhsOself :: Decls
              _lhsOlabels :: ([Label])
              _lhsOoffset :: Int
              _lhsOcodes =
                  {-# LINE 137 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  id
                  {-# LINE 355 "src/CCO/Imp/AG.hs" #-}
              _lhsOenv =
                  {-# LINE 67 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  []
                  {-# LINE 359 "src/CCO/Imp/AG.hs" #-}
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOlabels =
                  {-# LINE 16 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIlabels
                  {-# LINE 367 "src/CCO/Imp/AG.hs" #-}
              _lhsOoffset =
                  {-# LINE 37 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIoffset
                  {-# LINE 371 "src/CCO/Imp/AG.hs" #-}
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset,_lhsOself)))
-- Exp ---------------------------------------------------------
data Exp  = Add (Exp) (Exp) 
          | Call (Ident) (Exps) 
          | Div (Exp) (Exp) 
          | Eq (Exp) (Exp) 
          | False_ 
          | Gt (Exp) (Exp) 
          | Int (Int) 
          | Lt (Exp) (Exp) 
          | Mul (Exp) (Exp) 
          | Sub (Exp) (Exp) 
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
              ( String,CodeS,([Label]),Exp)
data Inh_Exp  = Inh_Exp {labels_Inh_Exp :: [Label],syms_Inh_Exp :: Syms}
data Syn_Exp  = Syn_Exp {ann_Syn_Exp :: String,codes_Syn_Exp :: CodeS,labels_Syn_Exp :: [Label],self_Syn_Exp :: Exp}
wrap_Exp :: T_Exp  ->
            Inh_Exp  ->
            Syn_Exp 
wrap_Exp sem (Inh_Exp _lhsIlabels _lhsIsyms )  =
    (let ( _lhsOann,_lhsOcodes,_lhsOlabels,_lhsOself) =
             (sem _lhsIlabels _lhsIsyms )
     in  (Syn_Exp _lhsOann _lhsOcodes _lhsOlabels _lhsOself ))
sem_Exp_Add :: T_Exp  ->
               T_Exp  ->
               T_Exp 
sem_Exp_Add e1_ e2_  =
    (\ _lhsIlabels
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOann :: String
              _lhsOself :: Exp
              _lhsOlabels :: ([Label])
              _e1Olabels :: ([Label])
              _e1Osyms :: Syms
              _e2Olabels :: ([Label])
              _e2Osyms :: Syms
              _e1Iann :: String
              _e1Icodes :: CodeS
              _e1Ilabels :: ([Label])
              _e1Iself :: Exp
              _e2Iann :: String
              _e2Icodes :: CodeS
              _e2Ilabels :: ([Label])
              _e2Iself :: Exp
              _ann =
                  {-# LINE 119 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _e1Iann ++ "+"  ++ _e2Iann
                  {-# LINE 451 "src/CCO/Imp/AG.hs" #-}
              _annote =
                  {-# LINE 130 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  annote SP 0 0 "green" _ann
                  {-# LINE 455 "src/CCO/Imp/AG.hs" #-}
              _lhsOcodes =
                  {-# LINE 179 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _e1Icodes . _e2Icodes . add . _annote
                  {-# LINE 459 "src/CCO/Imp/AG.hs" #-}
              _lhsOann =
                  {-# LINE 110 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _ann
                  {-# LINE 463 "src/CCO/Imp/AG.hs" #-}
              _self =
                  Add _e1Iself _e2Iself
              _lhsOself =
                  _self
              _lhsOlabels =
                  {-# LINE 16 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _e2Ilabels
                  {-# LINE 471 "src/CCO/Imp/AG.hs" #-}
              _e1Olabels =
                  {-# LINE 15 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIlabels
                  {-# LINE 475 "src/CCO/Imp/AG.hs" #-}
              _e1Osyms =
                  {-# LINE 98 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIsyms
                  {-# LINE 479 "src/CCO/Imp/AG.hs" #-}
              _e2Olabels =
                  {-# LINE 15 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _e1Ilabels
                  {-# LINE 483 "src/CCO/Imp/AG.hs" #-}
              _e2Osyms =
                  {-# LINE 98 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIsyms
                  {-# LINE 487 "src/CCO/Imp/AG.hs" #-}
              ( _e1Iann,_e1Icodes,_e1Ilabels,_e1Iself) =
                  (e1_ _e1Olabels _e1Osyms )
              ( _e2Iann,_e2Icodes,_e2Ilabels,_e2Iself) =
                  (e2_ _e2Olabels _e2Osyms )
          in  ( _lhsOann,_lhsOcodes,_lhsOlabels,_lhsOself)))
sem_Exp_Call :: Ident ->
                T_Exps  ->
                T_Exp 
sem_Exp_Call f_ es_  =
    (\ _lhsIlabels
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOann :: String
              _lhsOself :: Exp
              _lhsOlabels :: ([Label])
              _esOlabels :: ([Label])
              _esOsyms :: Syms
              _esIanns :: ([String])
              _esIcodes :: CodeS
              _esIlabels :: ([Label])
              _esIself :: Exps
              _ann =
                  {-# LINE 118 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  f_ ++ "(" ++ concat (intersperse "," _esIanns) ++ ")"
                  {-# LINE 512 "src/CCO/Imp/AG.hs" #-}
              _annote =
                  {-# LINE 130 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  annote SP 0 0 "green" _ann
                  {-# LINE 516 "src/CCO/Imp/AG.hs" #-}
              _lhsOcodes =
                  {-# LINE 178 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _esIcodes . call f_ _lhsIsyms
                  {-# LINE 520 "src/CCO/Imp/AG.hs" #-}
              _lhsOann =
                  {-# LINE 110 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _ann
                  {-# LINE 524 "src/CCO/Imp/AG.hs" #-}
              _self =
                  Call f_ _esIself
              _lhsOself =
                  _self
              _lhsOlabels =
                  {-# LINE 16 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _esIlabels
                  {-# LINE 532 "src/CCO/Imp/AG.hs" #-}
              _esOlabels =
                  {-# LINE 15 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIlabels
                  {-# LINE 536 "src/CCO/Imp/AG.hs" #-}
              _esOsyms =
                  {-# LINE 98 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIsyms
                  {-# LINE 540 "src/CCO/Imp/AG.hs" #-}
              ( _esIanns,_esIcodes,_esIlabels,_esIself) =
                  (es_ _esOlabels _esOsyms )
          in  ( _lhsOann,_lhsOcodes,_lhsOlabels,_lhsOself)))
sem_Exp_Div :: T_Exp  ->
               T_Exp  ->
               T_Exp 
sem_Exp_Div e1_ e2_  =
    (\ _lhsIlabels
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOann :: String
              _lhsOself :: Exp
              _lhsOlabels :: ([Label])
              _e1Olabels :: ([Label])
              _e1Osyms :: Syms
              _e2Olabels :: ([Label])
              _e2Osyms :: Syms
              _e1Iann :: String
              _e1Icodes :: CodeS
              _e1Ilabels :: ([Label])
              _e1Iself :: Exp
              _e2Iann :: String
              _e2Icodes :: CodeS
              _e2Ilabels :: ([Label])
              _e2Iself :: Exp
              _ann =
                  {-# LINE 122 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _e1Iann ++ "/"  ++ _e2Iann
                  {-# LINE 569 "src/CCO/Imp/AG.hs" #-}
              _annote =
                  {-# LINE 130 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  annote SP 0 0 "green" _ann
                  {-# LINE 573 "src/CCO/Imp/AG.hs" #-}
              _lhsOcodes =
                  {-# LINE 182 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _e1Icodes . _e2Icodes . div . _annote
                  {-# LINE 577 "src/CCO/Imp/AG.hs" #-}
              _lhsOann =
                  {-# LINE 110 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _ann
                  {-# LINE 581 "src/CCO/Imp/AG.hs" #-}
              _self =
                  Div _e1Iself _e2Iself
              _lhsOself =
                  _self
              _lhsOlabels =
                  {-# LINE 16 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _e2Ilabels
                  {-# LINE 589 "src/CCO/Imp/AG.hs" #-}
              _e1Olabels =
                  {-# LINE 15 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIlabels
                  {-# LINE 593 "src/CCO/Imp/AG.hs" #-}
              _e1Osyms =
                  {-# LINE 98 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIsyms
                  {-# LINE 597 "src/CCO/Imp/AG.hs" #-}
              _e2Olabels =
                  {-# LINE 15 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _e1Ilabels
                  {-# LINE 601 "src/CCO/Imp/AG.hs" #-}
              _e2Osyms =
                  {-# LINE 98 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIsyms
                  {-# LINE 605 "src/CCO/Imp/AG.hs" #-}
              ( _e1Iann,_e1Icodes,_e1Ilabels,_e1Iself) =
                  (e1_ _e1Olabels _e1Osyms )
              ( _e2Iann,_e2Icodes,_e2Ilabels,_e2Iself) =
                  (e2_ _e2Olabels _e2Osyms )
          in  ( _lhsOann,_lhsOcodes,_lhsOlabels,_lhsOself)))
sem_Exp_Eq :: T_Exp  ->
              T_Exp  ->
              T_Exp 
sem_Exp_Eq e1_ e2_  =
    (\ _lhsIlabels
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOann :: String
              _lhsOself :: Exp
              _lhsOlabels :: ([Label])
              _e1Olabels :: ([Label])
              _e1Osyms :: Syms
              _e2Olabels :: ([Label])
              _e2Osyms :: Syms
              _e1Iann :: String
              _e1Icodes :: CodeS
              _e1Ilabels :: ([Label])
              _e1Iself :: Exp
              _e2Iann :: String
              _e2Icodes :: CodeS
              _e2Ilabels :: ([Label])
              _e2Iself :: Exp
              _ann =
                  {-# LINE 124 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _e1Iann ++ "==" ++ _e2Iann
                  {-# LINE 636 "src/CCO/Imp/AG.hs" #-}
              _annote =
                  {-# LINE 130 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  annote SP 0 0 "green" _ann
                  {-# LINE 640 "src/CCO/Imp/AG.hs" #-}
              _lhsOcodes =
                  {-# LINE 184 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _e1Icodes . _e2Icodes . eq . _annote
                  {-# LINE 644 "src/CCO/Imp/AG.hs" #-}
              _lhsOann =
                  {-# LINE 110 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _ann
                  {-# LINE 648 "src/CCO/Imp/AG.hs" #-}
              _self =
                  Eq _e1Iself _e2Iself
              _lhsOself =
                  _self
              _lhsOlabels =
                  {-# LINE 16 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _e2Ilabels
                  {-# LINE 656 "src/CCO/Imp/AG.hs" #-}
              _e1Olabels =
                  {-# LINE 15 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIlabels
                  {-# LINE 660 "src/CCO/Imp/AG.hs" #-}
              _e1Osyms =
                  {-# LINE 98 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIsyms
                  {-# LINE 664 "src/CCO/Imp/AG.hs" #-}
              _e2Olabels =
                  {-# LINE 15 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _e1Ilabels
                  {-# LINE 668 "src/CCO/Imp/AG.hs" #-}
              _e2Osyms =
                  {-# LINE 98 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIsyms
                  {-# LINE 672 "src/CCO/Imp/AG.hs" #-}
              ( _e1Iann,_e1Icodes,_e1Ilabels,_e1Iself) =
                  (e1_ _e1Olabels _e1Osyms )
              ( _e2Iann,_e2Icodes,_e2Ilabels,_e2Iself) =
                  (e2_ _e2Olabels _e2Osyms )
          in  ( _lhsOann,_lhsOcodes,_lhsOlabels,_lhsOself)))
sem_Exp_False_ :: T_Exp 
sem_Exp_False_  =
    (\ _lhsIlabels
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOann :: String
              _lhsOself :: Exp
              _lhsOlabels :: ([Label])
              _ann =
                  {-# LINE 115 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  "False"
                  {-# LINE 689 "src/CCO/Imp/AG.hs" #-}
              _annote =
                  {-# LINE 130 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  annote SP 0 0 "green" _ann
                  {-# LINE 693 "src/CCO/Imp/AG.hs" #-}
              _lhsOcodes =
                  {-# LINE 175 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  ldc 0 . _annote
                  {-# LINE 697 "src/CCO/Imp/AG.hs" #-}
              _lhsOann =
                  {-# LINE 110 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _ann
                  {-# LINE 701 "src/CCO/Imp/AG.hs" #-}
              _self =
                  False_
              _lhsOself =
                  _self
              _lhsOlabels =
                  {-# LINE 16 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIlabels
                  {-# LINE 709 "src/CCO/Imp/AG.hs" #-}
          in  ( _lhsOann,_lhsOcodes,_lhsOlabels,_lhsOself)))
sem_Exp_Gt :: T_Exp  ->
              T_Exp  ->
              T_Exp 
sem_Exp_Gt e1_ e2_  =
    (\ _lhsIlabels
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOann :: String
              _lhsOself :: Exp
              _lhsOlabels :: ([Label])
              _e1Olabels :: ([Label])
              _e1Osyms :: Syms
              _e2Olabels :: ([Label])
              _e2Osyms :: Syms
              _e1Iann :: String
              _e1Icodes :: CodeS
              _e1Ilabels :: ([Label])
              _e1Iself :: Exp
              _e2Iann :: String
              _e2Icodes :: CodeS
              _e2Ilabels :: ([Label])
              _e2Iself :: Exp
              _ann =
                  {-# LINE 125 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _e1Iann ++ ">"  ++ _e2Iann
                  {-# LINE 736 "src/CCO/Imp/AG.hs" #-}
              _annote =
                  {-# LINE 130 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  annote SP 0 0 "green" _ann
                  {-# LINE 740 "src/CCO/Imp/AG.hs" #-}
              _lhsOcodes =
                  {-# LINE 185 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _e1Icodes . _e2Icodes . gt . _annote
                  {-# LINE 744 "src/CCO/Imp/AG.hs" #-}
              _lhsOann =
                  {-# LINE 110 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _ann
                  {-# LINE 748 "src/CCO/Imp/AG.hs" #-}
              _self =
                  Gt _e1Iself _e2Iself
              _lhsOself =
                  _self
              _lhsOlabels =
                  {-# LINE 16 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _e2Ilabels
                  {-# LINE 756 "src/CCO/Imp/AG.hs" #-}
              _e1Olabels =
                  {-# LINE 15 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIlabels
                  {-# LINE 760 "src/CCO/Imp/AG.hs" #-}
              _e1Osyms =
                  {-# LINE 98 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIsyms
                  {-# LINE 764 "src/CCO/Imp/AG.hs" #-}
              _e2Olabels =
                  {-# LINE 15 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _e1Ilabels
                  {-# LINE 768 "src/CCO/Imp/AG.hs" #-}
              _e2Osyms =
                  {-# LINE 98 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIsyms
                  {-# LINE 772 "src/CCO/Imp/AG.hs" #-}
              ( _e1Iann,_e1Icodes,_e1Ilabels,_e1Iself) =
                  (e1_ _e1Olabels _e1Osyms )
              ( _e2Iann,_e2Icodes,_e2Ilabels,_e2Iself) =
                  (e2_ _e2Olabels _e2Osyms )
          in  ( _lhsOann,_lhsOcodes,_lhsOlabels,_lhsOself)))
sem_Exp_Int :: Int ->
               T_Exp 
sem_Exp_Int n_  =
    (\ _lhsIlabels
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOann :: String
              _lhsOself :: Exp
              _lhsOlabels :: ([Label])
              _ann =
                  {-# LINE 114 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  show n_
                  {-# LINE 790 "src/CCO/Imp/AG.hs" #-}
              _annote =
                  {-# LINE 130 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  annote SP 0 0 "green" _ann
                  {-# LINE 794 "src/CCO/Imp/AG.hs" #-}
              _lhsOcodes =
                  {-# LINE 174 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  ldc n_ . _annote
                  {-# LINE 798 "src/CCO/Imp/AG.hs" #-}
              _lhsOann =
                  {-# LINE 110 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _ann
                  {-# LINE 802 "src/CCO/Imp/AG.hs" #-}
              _self =
                  Int n_
              _lhsOself =
                  _self
              _lhsOlabels =
                  {-# LINE 16 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIlabels
                  {-# LINE 810 "src/CCO/Imp/AG.hs" #-}
          in  ( _lhsOann,_lhsOcodes,_lhsOlabels,_lhsOself)))
sem_Exp_Lt :: T_Exp  ->
              T_Exp  ->
              T_Exp 
sem_Exp_Lt e1_ e2_  =
    (\ _lhsIlabels
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOann :: String
              _lhsOself :: Exp
              _lhsOlabels :: ([Label])
              _e1Olabels :: ([Label])
              _e1Osyms :: Syms
              _e2Olabels :: ([Label])
              _e2Osyms :: Syms
              _e1Iann :: String
              _e1Icodes :: CodeS
              _e1Ilabels :: ([Label])
              _e1Iself :: Exp
              _e2Iann :: String
              _e2Icodes :: CodeS
              _e2Ilabels :: ([Label])
              _e2Iself :: Exp
              _ann =
                  {-# LINE 123 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _e1Iann ++ "<"  ++ _e2Iann
                  {-# LINE 837 "src/CCO/Imp/AG.hs" #-}
              _annote =
                  {-# LINE 130 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  annote SP 0 0 "green" _ann
                  {-# LINE 841 "src/CCO/Imp/AG.hs" #-}
              _lhsOcodes =
                  {-# LINE 183 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _e1Icodes . _e2Icodes . lt . _annote
                  {-# LINE 845 "src/CCO/Imp/AG.hs" #-}
              _lhsOann =
                  {-# LINE 110 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _ann
                  {-# LINE 849 "src/CCO/Imp/AG.hs" #-}
              _self =
                  Lt _e1Iself _e2Iself
              _lhsOself =
                  _self
              _lhsOlabels =
                  {-# LINE 16 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _e2Ilabels
                  {-# LINE 857 "src/CCO/Imp/AG.hs" #-}
              _e1Olabels =
                  {-# LINE 15 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIlabels
                  {-# LINE 861 "src/CCO/Imp/AG.hs" #-}
              _e1Osyms =
                  {-# LINE 98 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIsyms
                  {-# LINE 865 "src/CCO/Imp/AG.hs" #-}
              _e2Olabels =
                  {-# LINE 15 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _e1Ilabels
                  {-# LINE 869 "src/CCO/Imp/AG.hs" #-}
              _e2Osyms =
                  {-# LINE 98 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIsyms
                  {-# LINE 873 "src/CCO/Imp/AG.hs" #-}
              ( _e1Iann,_e1Icodes,_e1Ilabels,_e1Iself) =
                  (e1_ _e1Olabels _e1Osyms )
              ( _e2Iann,_e2Icodes,_e2Ilabels,_e2Iself) =
                  (e2_ _e2Olabels _e2Osyms )
          in  ( _lhsOann,_lhsOcodes,_lhsOlabels,_lhsOself)))
sem_Exp_Mul :: T_Exp  ->
               T_Exp  ->
               T_Exp 
sem_Exp_Mul e1_ e2_  =
    (\ _lhsIlabels
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOann :: String
              _lhsOself :: Exp
              _lhsOlabels :: ([Label])
              _e1Olabels :: ([Label])
              _e1Osyms :: Syms
              _e2Olabels :: ([Label])
              _e2Osyms :: Syms
              _e1Iann :: String
              _e1Icodes :: CodeS
              _e1Ilabels :: ([Label])
              _e1Iself :: Exp
              _e2Iann :: String
              _e2Icodes :: CodeS
              _e2Ilabels :: ([Label])
              _e2Iself :: Exp
              _ann =
                  {-# LINE 121 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _e1Iann ++ "*"  ++ _e2Iann
                  {-# LINE 904 "src/CCO/Imp/AG.hs" #-}
              _annote =
                  {-# LINE 130 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  annote SP 0 0 "green" _ann
                  {-# LINE 908 "src/CCO/Imp/AG.hs" #-}
              _lhsOcodes =
                  {-# LINE 181 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _e1Icodes . _e2Icodes . mul . _annote
                  {-# LINE 912 "src/CCO/Imp/AG.hs" #-}
              _lhsOann =
                  {-# LINE 110 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _ann
                  {-# LINE 916 "src/CCO/Imp/AG.hs" #-}
              _self =
                  Mul _e1Iself _e2Iself
              _lhsOself =
                  _self
              _lhsOlabels =
                  {-# LINE 16 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _e2Ilabels
                  {-# LINE 924 "src/CCO/Imp/AG.hs" #-}
              _e1Olabels =
                  {-# LINE 15 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIlabels
                  {-# LINE 928 "src/CCO/Imp/AG.hs" #-}
              _e1Osyms =
                  {-# LINE 98 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIsyms
                  {-# LINE 932 "src/CCO/Imp/AG.hs" #-}
              _e2Olabels =
                  {-# LINE 15 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _e1Ilabels
                  {-# LINE 936 "src/CCO/Imp/AG.hs" #-}
              _e2Osyms =
                  {-# LINE 98 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIsyms
                  {-# LINE 940 "src/CCO/Imp/AG.hs" #-}
              ( _e1Iann,_e1Icodes,_e1Ilabels,_e1Iself) =
                  (e1_ _e1Olabels _e1Osyms )
              ( _e2Iann,_e2Icodes,_e2Ilabels,_e2Iself) =
                  (e2_ _e2Olabels _e2Osyms )
          in  ( _lhsOann,_lhsOcodes,_lhsOlabels,_lhsOself)))
sem_Exp_Sub :: T_Exp  ->
               T_Exp  ->
               T_Exp 
sem_Exp_Sub e1_ e2_  =
    (\ _lhsIlabels
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOann :: String
              _lhsOself :: Exp
              _lhsOlabels :: ([Label])
              _e1Olabels :: ([Label])
              _e1Osyms :: Syms
              _e2Olabels :: ([Label])
              _e2Osyms :: Syms
              _e1Iann :: String
              _e1Icodes :: CodeS
              _e1Ilabels :: ([Label])
              _e1Iself :: Exp
              _e2Iann :: String
              _e2Icodes :: CodeS
              _e2Ilabels :: ([Label])
              _e2Iself :: Exp
              _ann =
                  {-# LINE 120 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _e1Iann ++ "-"  ++ _e2Iann
                  {-# LINE 971 "src/CCO/Imp/AG.hs" #-}
              _annote =
                  {-# LINE 130 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  annote SP 0 0 "green" _ann
                  {-# LINE 975 "src/CCO/Imp/AG.hs" #-}
              _lhsOcodes =
                  {-# LINE 180 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _e1Icodes . _e2Icodes . sub . _annote
                  {-# LINE 979 "src/CCO/Imp/AG.hs" #-}
              _lhsOann =
                  {-# LINE 110 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _ann
                  {-# LINE 983 "src/CCO/Imp/AG.hs" #-}
              _self =
                  Sub _e1Iself _e2Iself
              _lhsOself =
                  _self
              _lhsOlabels =
                  {-# LINE 16 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _e2Ilabels
                  {-# LINE 991 "src/CCO/Imp/AG.hs" #-}
              _e1Olabels =
                  {-# LINE 15 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIlabels
                  {-# LINE 995 "src/CCO/Imp/AG.hs" #-}
              _e1Osyms =
                  {-# LINE 98 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIsyms
                  {-# LINE 999 "src/CCO/Imp/AG.hs" #-}
              _e2Olabels =
                  {-# LINE 15 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _e1Ilabels
                  {-# LINE 1003 "src/CCO/Imp/AG.hs" #-}
              _e2Osyms =
                  {-# LINE 98 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIsyms
                  {-# LINE 1007 "src/CCO/Imp/AG.hs" #-}
              ( _e1Iann,_e1Icodes,_e1Ilabels,_e1Iself) =
                  (e1_ _e1Olabels _e1Osyms )
              ( _e2Iann,_e2Icodes,_e2Ilabels,_e2Iself) =
                  (e2_ _e2Olabels _e2Osyms )
          in  ( _lhsOann,_lhsOcodes,_lhsOlabels,_lhsOself)))
sem_Exp_True_ :: T_Exp 
sem_Exp_True_  =
    (\ _lhsIlabels
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOann :: String
              _lhsOself :: Exp
              _lhsOlabels :: ([Label])
              _ann =
                  {-# LINE 116 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  "True"
                  {-# LINE 1024 "src/CCO/Imp/AG.hs" #-}
              _annote =
                  {-# LINE 130 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  annote SP 0 0 "green" _ann
                  {-# LINE 1028 "src/CCO/Imp/AG.hs" #-}
              _lhsOcodes =
                  {-# LINE 176 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  ldc 1 . _annote
                  {-# LINE 1032 "src/CCO/Imp/AG.hs" #-}
              _lhsOann =
                  {-# LINE 110 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _ann
                  {-# LINE 1036 "src/CCO/Imp/AG.hs" #-}
              _self =
                  True_
              _lhsOself =
                  _self
              _lhsOlabels =
                  {-# LINE 16 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIlabels
                  {-# LINE 1044 "src/CCO/Imp/AG.hs" #-}
          in  ( _lhsOann,_lhsOcodes,_lhsOlabels,_lhsOself)))
sem_Exp_Var :: Ident ->
               T_Exp 
sem_Exp_Var x_  =
    (\ _lhsIlabels
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOann :: String
              _lhsOself :: Exp
              _lhsOlabels :: ([Label])
              _ann =
                  {-# LINE 117 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  x_
                  {-# LINE 1058 "src/CCO/Imp/AG.hs" #-}
              _annote =
                  {-# LINE 130 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  annote SP 0 0 "green" _ann
                  {-# LINE 1062 "src/CCO/Imp/AG.hs" #-}
              _lhsOcodes =
                  {-# LINE 177 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  get x_ _lhsIsyms . _annote
                  {-# LINE 1066 "src/CCO/Imp/AG.hs" #-}
              _lhsOann =
                  {-# LINE 110 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _ann
                  {-# LINE 1070 "src/CCO/Imp/AG.hs" #-}
              _self =
                  Var x_
              _lhsOself =
                  _self
              _lhsOlabels =
                  {-# LINE 16 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIlabels
                  {-# LINE 1078 "src/CCO/Imp/AG.hs" #-}
          in  ( _lhsOann,_lhsOcodes,_lhsOlabels,_lhsOself)))
-- Exps --------------------------------------------------------
type Exps  = [(Exp)]
-- cata
sem_Exps :: Exps  ->
            T_Exps 
sem_Exps list  =
    (Prelude.foldr sem_Exps_Cons sem_Exps_Nil (Prelude.map sem_Exp list) )
-- semantic domain
type T_Exps  = ([Label]) ->
               Syms ->
               ( ([String]),CodeS,([Label]),Exps)
data Inh_Exps  = Inh_Exps {labels_Inh_Exps :: [Label],syms_Inh_Exps :: Syms}
data Syn_Exps  = Syn_Exps {anns_Syn_Exps :: [String],codes_Syn_Exps :: CodeS,labels_Syn_Exps :: [Label],self_Syn_Exps :: Exps}
wrap_Exps :: T_Exps  ->
             Inh_Exps  ->
             Syn_Exps 
wrap_Exps sem (Inh_Exps _lhsIlabels _lhsIsyms )  =
    (let ( _lhsOanns,_lhsOcodes,_lhsOlabels,_lhsOself) =
             (sem _lhsIlabels _lhsIsyms )
     in  (Syn_Exps _lhsOanns _lhsOcodes _lhsOlabels _lhsOself ))
sem_Exps_Cons :: T_Exp  ->
                 T_Exps  ->
                 T_Exps 
sem_Exps_Cons hd_ tl_  =
    (\ _lhsIlabels
       _lhsIsyms ->
         (let _lhsOanns :: ([String])
              _lhsOcodes :: CodeS
              _lhsOself :: Exps
              _lhsOlabels :: ([Label])
              _hdOlabels :: ([Label])
              _hdOsyms :: Syms
              _tlOlabels :: ([Label])
              _tlOsyms :: Syms
              _hdIann :: String
              _hdIcodes :: CodeS
              _hdIlabels :: ([Label])
              _hdIself :: Exp
              _tlIanns :: ([String])
              _tlIcodes :: CodeS
              _tlIlabels :: ([Label])
              _tlIself :: Exps
              _lhsOanns =
                  {-# LINE 128 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _hdIann : _tlIanns
                  {-# LINE 1125 "src/CCO/Imp/AG.hs" #-}
              _lhsOcodes =
                  {-# LINE 137 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _hdIcodes . _tlIcodes
                  {-# LINE 1129 "src/CCO/Imp/AG.hs" #-}
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOlabels =
                  {-# LINE 16 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _tlIlabels
                  {-# LINE 1137 "src/CCO/Imp/AG.hs" #-}
              _hdOlabels =
                  {-# LINE 15 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIlabels
                  {-# LINE 1141 "src/CCO/Imp/AG.hs" #-}
              _hdOsyms =
                  {-# LINE 98 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIsyms
                  {-# LINE 1145 "src/CCO/Imp/AG.hs" #-}
              _tlOlabels =
                  {-# LINE 15 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _hdIlabels
                  {-# LINE 1149 "src/CCO/Imp/AG.hs" #-}
              _tlOsyms =
                  {-# LINE 98 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIsyms
                  {-# LINE 1153 "src/CCO/Imp/AG.hs" #-}
              ( _hdIann,_hdIcodes,_hdIlabels,_hdIself) =
                  (hd_ _hdOlabels _hdOsyms )
              ( _tlIanns,_tlIcodes,_tlIlabels,_tlIself) =
                  (tl_ _tlOlabels _tlOsyms )
          in  ( _lhsOanns,_lhsOcodes,_lhsOlabels,_lhsOself)))
sem_Exps_Nil :: T_Exps 
sem_Exps_Nil  =
    (\ _lhsIlabels
       _lhsIsyms ->
         (let _lhsOanns :: ([String])
              _lhsOcodes :: CodeS
              _lhsOself :: Exps
              _lhsOlabels :: ([Label])
              _lhsOanns =
                  {-# LINE 127 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  []
                  {-# LINE 1170 "src/CCO/Imp/AG.hs" #-}
              _lhsOcodes =
                  {-# LINE 137 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  id
                  {-# LINE 1174 "src/CCO/Imp/AG.hs" #-}
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOlabels =
                  {-# LINE 16 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIlabels
                  {-# LINE 1182 "src/CCO/Imp/AG.hs" #-}
          in  ( _lhsOanns,_lhsOcodes,_lhsOlabels,_lhsOself)))
-- Prog --------------------------------------------------------
data Prog  = TopLevelDecls (Decls) 
-- cata
sem_Prog :: Prog  ->
            T_Prog 
sem_Prog (TopLevelDecls _ds )  =
    (sem_Prog_TopLevelDecls (sem_Decls _ds ) )
-- semantic domain
type T_Prog  = ( Code,Prog)
data Inh_Prog  = Inh_Prog {}
data Syn_Prog  = Syn_Prog {code_Syn_Prog :: Code,self_Syn_Prog :: Prog}
wrap_Prog :: T_Prog  ->
             Inh_Prog  ->
             Syn_Prog 
wrap_Prog sem (Inh_Prog )  =
    (let ( _lhsOcode,_lhsOself) =
             (sem )
     in  (Syn_Prog _lhsOcode _lhsOself ))
sem_Prog_TopLevelDecls :: T_Decls  ->
                          T_Prog 
sem_Prog_TopLevelDecls ds_  =
    (let _dsOlabels :: ([Label])
         _dsOoffset :: Int
         _dsOsyms :: Syms
         _lhsOcode :: Code
         _lhsOself :: Prog
         _dsIcodes :: CodeS
         _dsIenv :: Env
         _dsIlabels :: ([Label])
         _dsIoffset :: Int
         _dsIself :: Decls
         _dsOlabels =
             {-# LINE 18 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
             [0 ..]
             {-# LINE 1218 "src/CCO/Imp/AG.hs" #-}
         _dsOoffset =
             {-# LINE 39 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
             1
             {-# LINE 1222 "src/CCO/Imp/AG.hs" #-}
         _dsOsyms =
             {-# LINE 100 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
             [_dsIenv]
             {-# LINE 1226 "src/CCO/Imp/AG.hs" #-}
         _codes =
             {-# LINE 139 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
             _dsIcodes .
             enter _dsIenv .
             call "main" [_dsIenv] .
             ajs (- 1) .
             exit _dsIenv
             {-# LINE 1234 "src/CCO/Imp/AG.hs" #-}
         _lhsOcode =
             {-# LINE 190 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
             Code (_codes     [])
             {-# LINE 1238 "src/CCO/Imp/AG.hs" #-}
         _self =
             TopLevelDecls _dsIself
         _lhsOself =
             _self
         ( _dsIcodes,_dsIenv,_dsIlabels,_dsIoffset,_dsIself) =
             (ds_ _dsOlabels _dsOoffset _dsOsyms )
     in  ( _lhsOcode,_lhsOself))
-- Stmt --------------------------------------------------------
data Stmt  = Assign (Ident) (Exp) 
           | Block (Stmts) 
           | Call_ (Ident) (Exps) 
           | Decl (Decl) 
           | Empty 
           | If (Exp) (Stmt) (Stmt) 
           | Print (Exp) 
           | Return (Exp) 
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
               ( CodeS,Env,([Label]),Int,Stmt)
data Inh_Stmt  = Inh_Stmt {labels_Inh_Stmt :: [Label],offset_Inh_Stmt :: Int,syms_Inh_Stmt :: Syms}
data Syn_Stmt  = Syn_Stmt {codes_Syn_Stmt :: CodeS,env_Syn_Stmt :: Env,labels_Syn_Stmt :: [Label],offset_Syn_Stmt :: Int,self_Syn_Stmt :: Stmt}
wrap_Stmt :: T_Stmt  ->
             Inh_Stmt  ->
             Syn_Stmt 
wrap_Stmt sem (Inh_Stmt _lhsIlabels _lhsIoffset _lhsIsyms )  =
    (let ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset,_lhsOself) =
             (sem _lhsIlabels _lhsIoffset _lhsIsyms )
     in  (Syn_Stmt _lhsOcodes _lhsOenv _lhsOlabels _lhsOoffset _lhsOself ))
sem_Stmt_Assign :: Ident ->
                   T_Exp  ->
                   T_Stmt 
sem_Stmt_Assign x_ e_  =
    (\ _lhsIlabels
       _lhsIoffset
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOenv :: Env
              _lhsOself :: Stmt
              _lhsOlabels :: ([Label])
              _lhsOoffset :: Int
              _eOlabels :: ([Label])
              _eOsyms :: Syms
              _eIann :: String
              _eIcodes :: CodeS
              _eIlabels :: ([Label])
              _eIself :: Exp
              _lhsOcodes =
                  {-# LINE 157 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _eIcodes . set x_ _lhsIsyms
                  {-# LINE 1309 "src/CCO/Imp/AG.hs" #-}
              _lhsOenv =
                  {-# LINE 67 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  []
                  {-# LINE 1313 "src/CCO/Imp/AG.hs" #-}
              _self =
                  Assign x_ _eIself
              _lhsOself =
                  _self
              _lhsOlabels =
                  {-# LINE 16 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _eIlabels
                  {-# LINE 1321 "src/CCO/Imp/AG.hs" #-}
              _lhsOoffset =
                  {-# LINE 37 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIoffset
                  {-# LINE 1325 "src/CCO/Imp/AG.hs" #-}
              _eOlabels =
                  {-# LINE 15 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIlabels
                  {-# LINE 1329 "src/CCO/Imp/AG.hs" #-}
              _eOsyms =
                  {-# LINE 98 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIsyms
                  {-# LINE 1333 "src/CCO/Imp/AG.hs" #-}
              ( _eIann,_eIcodes,_eIlabels,_eIself) =
                  (e_ _eOlabels _eOsyms )
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset,_lhsOself)))
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
              _lhsOself :: Stmt
              _lhsOlabels :: ([Label])
              _bOlabels :: ([Label])
              _bOoffset :: Int
              _bIcodes :: CodeS
              _bIenv :: Env
              _bIlabels :: ([Label])
              _bIoffset :: Int
              _bIself :: Stmts
              _lhsOoffset =
                  {-# LINE 42 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIoffset
                  {-# LINE 1359 "src/CCO/Imp/AG.hs" #-}
              _lhsOenv =
                  {-# LINE 72 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  []
                  {-# LINE 1363 "src/CCO/Imp/AG.hs" #-}
              _bOsyms =
                  {-# LINE 102 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  let local : global = _lhsIsyms
                  in  (local ++ _bIenv) : global
                  {-# LINE 1368 "src/CCO/Imp/AG.hs" #-}
              _lhsOcodes =
                  {-# LINE 170 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  enter _bIenv .
                  _bIcodes .
                  exit _bIenv
                  {-# LINE 1374 "src/CCO/Imp/AG.hs" #-}
              _self =
                  Block _bIself
              _lhsOself =
                  _self
              _lhsOlabels =
                  {-# LINE 16 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _bIlabels
                  {-# LINE 1382 "src/CCO/Imp/AG.hs" #-}
              _bOlabels =
                  {-# LINE 15 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIlabels
                  {-# LINE 1386 "src/CCO/Imp/AG.hs" #-}
              _bOoffset =
                  {-# LINE 36 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIoffset
                  {-# LINE 1390 "src/CCO/Imp/AG.hs" #-}
              ( _bIcodes,_bIenv,_bIlabels,_bIoffset,_bIself) =
                  (b_ _bOlabels _bOoffset _bOsyms )
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset,_lhsOself)))
sem_Stmt_Call_ :: Ident ->
                  T_Exps  ->
                  T_Stmt 
sem_Stmt_Call_ f_ es_  =
    (\ _lhsIlabels
       _lhsIoffset
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOenv :: Env
              _lhsOself :: Stmt
              _lhsOlabels :: ([Label])
              _lhsOoffset :: Int
              _esOlabels :: ([Label])
              _esOsyms :: Syms
              _esIanns :: ([String])
              _esIcodes :: CodeS
              _esIlabels :: ([Label])
              _esIself :: Exps
              _lhsOcodes =
                  {-# LINE 158 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _esIcodes .
                  call f_ _lhsIsyms .
                  ajs (- 1)
                  {-# LINE 1417 "src/CCO/Imp/AG.hs" #-}
              _lhsOenv =
                  {-# LINE 67 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  []
                  {-# LINE 1421 "src/CCO/Imp/AG.hs" #-}
              _self =
                  Call_ f_ _esIself
              _lhsOself =
                  _self
              _lhsOlabels =
                  {-# LINE 16 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _esIlabels
                  {-# LINE 1429 "src/CCO/Imp/AG.hs" #-}
              _lhsOoffset =
                  {-# LINE 37 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIoffset
                  {-# LINE 1433 "src/CCO/Imp/AG.hs" #-}
              _esOlabels =
                  {-# LINE 15 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIlabels
                  {-# LINE 1437 "src/CCO/Imp/AG.hs" #-}
              _esOsyms =
                  {-# LINE 98 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIsyms
                  {-# LINE 1441 "src/CCO/Imp/AG.hs" #-}
              ( _esIanns,_esIcodes,_esIlabels,_esIself) =
                  (es_ _esOlabels _esOsyms )
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset,_lhsOself)))
sem_Stmt_Decl :: T_Decl  ->
                 T_Stmt 
sem_Stmt_Decl d_  =
    (\ _lhsIlabels
       _lhsIoffset
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOenv :: Env
              _lhsOself :: Stmt
              _lhsOlabels :: ([Label])
              _lhsOoffset :: Int
              _dOlabels :: ([Label])
              _dOoffset :: Int
              _dOsyms :: Syms
              _dIcodes :: CodeS
              _dIenv :: Env
              _dIlabels :: ([Label])
              _dIoffset :: Int
              _dIself :: Decl
              _lhsOcodes =
                  {-# LINE 137 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _dIcodes
                  {-# LINE 1467 "src/CCO/Imp/AG.hs" #-}
              _lhsOenv =
                  {-# LINE 67 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _dIenv
                  {-# LINE 1471 "src/CCO/Imp/AG.hs" #-}
              _self =
                  Decl _dIself
              _lhsOself =
                  _self
              _lhsOlabels =
                  {-# LINE 16 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _dIlabels
                  {-# LINE 1479 "src/CCO/Imp/AG.hs" #-}
              _lhsOoffset =
                  {-# LINE 37 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _dIoffset
                  {-# LINE 1483 "src/CCO/Imp/AG.hs" #-}
              _dOlabels =
                  {-# LINE 15 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIlabels
                  {-# LINE 1487 "src/CCO/Imp/AG.hs" #-}
              _dOoffset =
                  {-# LINE 36 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIoffset
                  {-# LINE 1491 "src/CCO/Imp/AG.hs" #-}
              _dOsyms =
                  {-# LINE 98 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIsyms
                  {-# LINE 1495 "src/CCO/Imp/AG.hs" #-}
              ( _dIcodes,_dIenv,_dIlabels,_dIoffset,_dIself) =
                  (d_ _dOlabels _dOoffset _dOsyms )
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset,_lhsOself)))
sem_Stmt_Empty :: T_Stmt 
sem_Stmt_Empty  =
    (\ _lhsIlabels
       _lhsIoffset
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOenv :: Env
              _lhsOself :: Stmt
              _lhsOlabels :: ([Label])
              _lhsOoffset :: Int
              _lhsOcodes =
                  {-# LINE 137 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  id
                  {-# LINE 1512 "src/CCO/Imp/AG.hs" #-}
              _lhsOenv =
                  {-# LINE 67 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  []
                  {-# LINE 1516 "src/CCO/Imp/AG.hs" #-}
              _self =
                  Empty
              _lhsOself =
                  _self
              _lhsOlabels =
                  {-# LINE 16 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIlabels
                  {-# LINE 1524 "src/CCO/Imp/AG.hs" #-}
              _lhsOoffset =
                  {-# LINE 37 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIoffset
                  {-# LINE 1528 "src/CCO/Imp/AG.hs" #-}
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset,_lhsOself)))
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
              _lhsOself :: Stmt
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
              _eIself :: Exp
              _s1Icodes :: CodeS
              _s1Ienv :: Env
              _s1Ilabels :: ([Label])
              _s1Ioffset :: Int
              _s1Iself :: Stmt
              _s2Icodes :: CodeS
              _s2Ienv :: Env
              _s2Ilabels :: ([Label])
              _s2Ioffset :: Int
              _s2Iself :: Stmt
              _elseLabel =
                  {-# LINE 24 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIlabels !! 0
                  {-# LINE 1568 "src/CCO/Imp/AG.hs" #-}
              _fiLabel =
                  {-# LINE 25 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIlabels !! 1
                  {-# LINE 1572 "src/CCO/Imp/AG.hs" #-}
              _eOlabels =
                  {-# LINE 26 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  drop 2 _lhsIlabels
                  {-# LINE 1576 "src/CCO/Imp/AG.hs" #-}
              _lhsOcodes =
                  {-# LINE 163 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _eIcodes .
                  brf _elseLabel     .
                  _s1Icodes .
                  bra _fiLabel     .
                  label _elseLabel     .
                    _s2Icodes .
                  label _fiLabel
                  {-# LINE 1586 "src/CCO/Imp/AG.hs" #-}
              _lhsOenv =
                  {-# LINE 67 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _s1Ienv ++ _s2Ienv
                  {-# LINE 1590 "src/CCO/Imp/AG.hs" #-}
              _self =
                  If _eIself _s1Iself _s2Iself
              _lhsOself =
                  _self
              _lhsOlabels =
                  {-# LINE 16 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _s2Ilabels
                  {-# LINE 1598 "src/CCO/Imp/AG.hs" #-}
              _lhsOoffset =
                  {-# LINE 37 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _s2Ioffset
                  {-# LINE 1602 "src/CCO/Imp/AG.hs" #-}
              _eOsyms =
                  {-# LINE 98 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIsyms
                  {-# LINE 1606 "src/CCO/Imp/AG.hs" #-}
              _s1Olabels =
                  {-# LINE 15 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _eIlabels
                  {-# LINE 1610 "src/CCO/Imp/AG.hs" #-}
              _s1Ooffset =
                  {-# LINE 36 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIoffset
                  {-# LINE 1614 "src/CCO/Imp/AG.hs" #-}
              _s1Osyms =
                  {-# LINE 98 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIsyms
                  {-# LINE 1618 "src/CCO/Imp/AG.hs" #-}
              _s2Olabels =
                  {-# LINE 15 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _s1Ilabels
                  {-# LINE 1622 "src/CCO/Imp/AG.hs" #-}
              _s2Ooffset =
                  {-# LINE 36 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _s1Ioffset
                  {-# LINE 1626 "src/CCO/Imp/AG.hs" #-}
              _s2Osyms =
                  {-# LINE 98 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIsyms
                  {-# LINE 1630 "src/CCO/Imp/AG.hs" #-}
              ( _eIann,_eIcodes,_eIlabels,_eIself) =
                  (e_ _eOlabels _eOsyms )
              ( _s1Icodes,_s1Ienv,_s1Ilabels,_s1Ioffset,_s1Iself) =
                  (s1_ _s1Olabels _s1Ooffset _s1Osyms )
              ( _s2Icodes,_s2Ienv,_s2Ilabels,_s2Ioffset,_s2Iself) =
                  (s2_ _s2Olabels _s2Ooffset _s2Osyms )
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset,_lhsOself)))
sem_Stmt_Print :: T_Exp  ->
                  T_Stmt 
sem_Stmt_Print e_  =
    (\ _lhsIlabels
       _lhsIoffset
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOenv :: Env
              _lhsOself :: Stmt
              _lhsOlabels :: ([Label])
              _lhsOoffset :: Int
              _eOlabels :: ([Label])
              _eOsyms :: Syms
              _eIann :: String
              _eIcodes :: CodeS
              _eIlabels :: ([Label])
              _eIself :: Exp
              _lhsOcodes =
                  {-# LINE 161 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _eIcodes . trap 0
                  {-# LINE 1658 "src/CCO/Imp/AG.hs" #-}
              _lhsOenv =
                  {-# LINE 67 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  []
                  {-# LINE 1662 "src/CCO/Imp/AG.hs" #-}
              _self =
                  Print _eIself
              _lhsOself =
                  _self
              _lhsOlabels =
                  {-# LINE 16 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _eIlabels
                  {-# LINE 1670 "src/CCO/Imp/AG.hs" #-}
              _lhsOoffset =
                  {-# LINE 37 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIoffset
                  {-# LINE 1674 "src/CCO/Imp/AG.hs" #-}
              _eOlabels =
                  {-# LINE 15 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIlabels
                  {-# LINE 1678 "src/CCO/Imp/AG.hs" #-}
              _eOsyms =
                  {-# LINE 98 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIsyms
                  {-# LINE 1682 "src/CCO/Imp/AG.hs" #-}
              ( _eIann,_eIcodes,_eIlabels,_eIself) =
                  (e_ _eOlabels _eOsyms )
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset,_lhsOself)))
sem_Stmt_Return :: T_Exp  ->
                   T_Stmt 
sem_Stmt_Return e_  =
    (\ _lhsIlabels
       _lhsIoffset
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOenv :: Env
              _lhsOself :: Stmt
              _lhsOlabels :: ([Label])
              _lhsOoffset :: Int
              _eOlabels :: ([Label])
              _eOsyms :: Syms
              _eIann :: String
              _eIcodes :: CodeS
              _eIlabels :: ([Label])
              _eIself :: Exp
              _lhsOcodes =
                  {-# LINE 162 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _eIcodes . return_ _lhsIsyms
                  {-# LINE 1706 "src/CCO/Imp/AG.hs" #-}
              _lhsOenv =
                  {-# LINE 67 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  []
                  {-# LINE 1710 "src/CCO/Imp/AG.hs" #-}
              _self =
                  Return _eIself
              _lhsOself =
                  _self
              _lhsOlabels =
                  {-# LINE 16 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _eIlabels
                  {-# LINE 1718 "src/CCO/Imp/AG.hs" #-}
              _lhsOoffset =
                  {-# LINE 37 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIoffset
                  {-# LINE 1722 "src/CCO/Imp/AG.hs" #-}
              _eOlabels =
                  {-# LINE 15 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIlabels
                  {-# LINE 1726 "src/CCO/Imp/AG.hs" #-}
              _eOsyms =
                  {-# LINE 98 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIsyms
                  {-# LINE 1730 "src/CCO/Imp/AG.hs" #-}
              ( _eIann,_eIcodes,_eIlabels,_eIself) =
                  (e_ _eOlabels _eOsyms )
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset,_lhsOself)))
-- Stmts -------------------------------------------------------
type Stmts  = [(Stmt)]
-- cata
sem_Stmts :: Stmts  ->
             T_Stmts 
sem_Stmts list  =
    (Prelude.foldr sem_Stmts_Cons sem_Stmts_Nil (Prelude.map sem_Stmt list) )
-- semantic domain
type T_Stmts  = ([Label]) ->
                Int ->
                Syms ->
                ( CodeS,Env,([Label]),Int,Stmts)
data Inh_Stmts  = Inh_Stmts {labels_Inh_Stmts :: [Label],offset_Inh_Stmts :: Int,syms_Inh_Stmts :: Syms}
data Syn_Stmts  = Syn_Stmts {codes_Syn_Stmts :: CodeS,env_Syn_Stmts :: Env,labels_Syn_Stmts :: [Label],offset_Syn_Stmts :: Int,self_Syn_Stmts :: Stmts}
wrap_Stmts :: T_Stmts  ->
              Inh_Stmts  ->
              Syn_Stmts 
wrap_Stmts sem (Inh_Stmts _lhsIlabels _lhsIoffset _lhsIsyms )  =
    (let ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset,_lhsOself) =
             (sem _lhsIlabels _lhsIoffset _lhsIsyms )
     in  (Syn_Stmts _lhsOcodes _lhsOenv _lhsOlabels _lhsOoffset _lhsOself ))
sem_Stmts_Cons :: T_Stmt  ->
                  T_Stmts  ->
                  T_Stmts 
sem_Stmts_Cons hd_ tl_  =
    (\ _lhsIlabels
       _lhsIoffset
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOenv :: Env
              _lhsOself :: Stmts
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
              _hdIself :: Stmt
              _tlIcodes :: CodeS
              _tlIenv :: Env
              _tlIlabels :: ([Label])
              _tlIoffset :: Int
              _tlIself :: Stmts
              _lhsOcodes =
                  {-# LINE 137 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _hdIcodes . _tlIcodes
                  {-# LINE 1786 "src/CCO/Imp/AG.hs" #-}
              _lhsOenv =
                  {-# LINE 67 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _hdIenv ++ _tlIenv
                  {-# LINE 1790 "src/CCO/Imp/AG.hs" #-}
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOlabels =
                  {-# LINE 16 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _tlIlabels
                  {-# LINE 1798 "src/CCO/Imp/AG.hs" #-}
              _lhsOoffset =
                  {-# LINE 37 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _tlIoffset
                  {-# LINE 1802 "src/CCO/Imp/AG.hs" #-}
              _hdOlabels =
                  {-# LINE 15 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIlabels
                  {-# LINE 1806 "src/CCO/Imp/AG.hs" #-}
              _hdOoffset =
                  {-# LINE 36 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIoffset
                  {-# LINE 1810 "src/CCO/Imp/AG.hs" #-}
              _hdOsyms =
                  {-# LINE 98 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIsyms
                  {-# LINE 1814 "src/CCO/Imp/AG.hs" #-}
              _tlOlabels =
                  {-# LINE 15 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _hdIlabels
                  {-# LINE 1818 "src/CCO/Imp/AG.hs" #-}
              _tlOoffset =
                  {-# LINE 36 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _hdIoffset
                  {-# LINE 1822 "src/CCO/Imp/AG.hs" #-}
              _tlOsyms =
                  {-# LINE 98 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIsyms
                  {-# LINE 1826 "src/CCO/Imp/AG.hs" #-}
              ( _hdIcodes,_hdIenv,_hdIlabels,_hdIoffset,_hdIself) =
                  (hd_ _hdOlabels _hdOoffset _hdOsyms )
              ( _tlIcodes,_tlIenv,_tlIlabels,_tlIoffset,_tlIself) =
                  (tl_ _tlOlabels _tlOoffset _tlOsyms )
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset,_lhsOself)))
sem_Stmts_Nil :: T_Stmts 
sem_Stmts_Nil  =
    (\ _lhsIlabels
       _lhsIoffset
       _lhsIsyms ->
         (let _lhsOcodes :: CodeS
              _lhsOenv :: Env
              _lhsOself :: Stmts
              _lhsOlabels :: ([Label])
              _lhsOoffset :: Int
              _lhsOcodes =
                  {-# LINE 137 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  id
                  {-# LINE 1845 "src/CCO/Imp/AG.hs" #-}
              _lhsOenv =
                  {-# LINE 67 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  []
                  {-# LINE 1849 "src/CCO/Imp/AG.hs" #-}
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOlabels =
                  {-# LINE 16 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIlabels
                  {-# LINE 1857 "src/CCO/Imp/AG.hs" #-}
              _lhsOoffset =
                  {-# LINE 37 "src/CCO/Imp/AG/CodeGeneration.ag" #-}
                  _lhsIoffset
                  {-# LINE 1861 "src/CCO/Imp/AG.hs" #-}
          in  ( _lhsOcodes,_lhsOenv,_lhsOlabels,_lhsOoffset,_lhsOself)))