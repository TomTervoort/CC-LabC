-------------------------------------------------------------------------------
-- |
-- Module      :  CCO.Ssm
-- Copyright   :  (c) 2008 Utrecht University
-- License     :  All rights reserved
--
-- Maintainer  :  stefan@cs.uu.nl
-- Stability   :  provisional
-- Portability :  portable
--
-- Code for the so-called Simple Stack Machine (SSM).
--
-------------------------------------------------------------------------------

module CCO.Ssm (
    -- * Machine code
    Label                -- = Int
  , Const                -- = Int
  , Offset               -- = Int
  , Register (SP, MP)    -- instances: Tree, Printable
  , Instruction (..)     -- instances: Tree, Printable
  , Code (Code)          -- instances: Tree, Printable

    -- * Support for code generation
  , CodeS                -- = [Instruction] -> [Instruction]
  , ldc                  -- :: Const -> CodeS
  , ldcL                 -- :: Label -> CodeS
  , lds                  -- :: Offset -> CodeS
  , ldl                  -- :: Offset -> CodeS
  , lda                  -- :: Offset -> CodeS
  , ldr                  -- :: Register -> CodeS
  , ldrr                 -- :: Register -> Register -> CodeS
  , sts                  -- :: Offset -> CodeS
  , stl                  -- :: Offset -> CodeS
  , sta                  -- :: Offset -> CodeS
  , str                  -- :: Register -> CodeS
  , ajs                  -- :: Offset -> CodeS
  , add                  -- :: CodeS
  , sub                  -- :: CodeS
  , mul                  -- :: CodeS
  , div                  -- :: CodeS
  , eq                   -- :: CodeS
  , lt                   -- :: CodeS
  , gt                   -- :: CodeS
  , bra                  -- :: Label -> CodeS
  , brf                  -- :: Label -> CodeS
  , jsr                  -- :: CodeS
  , ret                  -- :: CodeS
  , nop                  -- :: CodeS
  , trap                 -- :: Const -> CodeS
  , halt                 -- :: CodeS
  , annote               -- :: Register -> Offset -> Offset -> String -> String -> CodeS
  , label                -- :: Label -> CodeS
) where

import CCO.Printing
import CCO.Tree              (ATerm (App), Tree (fromTree, toTree))
import CCO.Tree.Parser       (parseTree, app, arg)
import Control.Applicative   (Applicative (pure, (<*>)), (<$>))
import Prelude hiding (div)

-------------------------------------------------------------------------------
-- Machine code
-------------------------------------------------------------------------------

type Label  = Int    -- ^ Type of labels.
type Const  = Int    -- ^ Type of constant operands.
type Offset = Int    -- ^ Type of stack offsets.

-- | Type of registers.
data Register
  = SP    -- ^ Stack pointer.
  | MP    -- ^ Mark pointer.

instance Tree Register where
  fromTree SP = App "SP" []
  fromTree MP = App "MP" []

  toTree = parseTree [ app "SP" (pure SP)
                     , app "MP" (pure MP)
                     ]

instance Printable Register where
  pp SP = text "SP"
  pp MP = text "MP"

-- | Type of SSM instructions.
data Instruction
    -- Copying
  = Ldc Const                 -- ^ Load constant.
  | LdcL Label                -- ^ Load label.
  | Lds Offset                -- ^ Load from stack.
  | Ldl Offset                -- ^ Load local.
  | Lda Offset                -- ^ Load via address.
  | Ldr Register              -- ^ Load register.
  | Ldrr Register Register    -- ^ Load register from register.
  | Sts Offset                -- ^ Store into stack.
  | Stl Offset                -- ^ Store local.
  | Sta Offset                -- ^ Store via address.
  | Str Register              -- ^ Store register.

    -- Convenience
  | Ajs Offset                -- ^ Adjust stack.

    -- Arithmetic
  | Add                       -- ^ Addition. 
  | Sub                       -- ^ Subtraction.
  | Mul                       -- ^ Multiplication.
  | Div                       -- ^ Division.
  | Eq                        -- ^ Test for equal.
  | Lt                        -- ^ Test for less than.
  | Gt                        -- ^ Test for greater than.

    -- Control
  | Bra Label                 -- ^ Unconditional branch.
  | Brf Label                 -- ^ Branch on false.
  | Jsr                       -- ^ Jump to subroutine.
  | Ret                       -- ^ Return.

    -- Other
  | Nop                       -- ^ No operation.
  | Trap Const                -- ^ Trap to environment.
  | Halt                      -- ^ Halt execution.

    -- Pseudoinstructions
  | Annote Register Offset Offset String String		-- ^ annotate stack contents with color and text
  | Label Label               -- ^ Label.    

instance Tree Instruction where
  fromTree (Ldc c)      = App "Ldc"   [fromTree c]
  fromTree (LdcL l)     = App "LdcL"  [fromTree l]
  fromTree (Lds i)      = App "Lds"   [fromTree i]
  fromTree (Ldl i)      = App "Ldl"   [fromTree i]
  fromTree (Lda i)      = App "Lda"   [fromTree i]
  fromTree (Ldr r)      = App "Ldr"   [fromTree r]
  fromTree (Ldrr r1 r2) = App "Ldrr"  [fromTree r1, fromTree r2]
  fromTree (Sts i)      = App "Sts"   [fromTree i]
  fromTree (Stl i)      = App "Stl"   [fromTree i]
  fromTree (Sta i)      = App "Sta"   [fromTree i]
  fromTree (Str r)      = App "Str"   [fromTree r]
  fromTree (Ajs i)      = App "Ajs"   [fromTree i]
  fromTree Add          = App "Add"   []
  fromTree Sub          = App "Sub"   []
  fromTree Mul          = App "Mul"   []
  fromTree Div          = App "Div"   []
  fromTree Eq           = App "Eq"    []
  fromTree Lt           = App "Lt"    []
  fromTree Gt           = App "Gt"    []
  fromTree (Bra l)      = App "Bra"   [fromTree l]
  fromTree (Brf l)      = App "Brf"   [fromTree l]
  fromTree Jsr          = App "Jsr"   []
  fromTree Ret          = App "Ret"   []
  fromTree Nop          = App "Nop"   []
  fromTree (Trap c)     = App "Trap"  [fromTree c]
  fromTree Halt         = App "Halt"  []
  fromTree (Annote r l h c i)
                        = App "Label" [fromTree r, fromTree l, fromTree h, fromTree c, fromTree i]
  fromTree (Label l)    = App "Label" [fromTree l]

  toTree = parseTree [ app "Ldc"    (Ldc <$> arg)
                     , app "LdcL"   (LdcL <$> arg)
                     , app "Lds"    (Lds <$> arg)
                     , app "Ldl"    (Ldl <$> arg)
                     , app "Lda"    (Lda <$> arg)
                     , app "Ldr"    (Ldr <$> arg)
                     , app "Ldrr"   (Ldrr <$> arg <*> arg)
                     , app "Sts"    (Sts <$> arg)
                     , app "Stl"    (Stl <$> arg)
                     , app "Sta"    (Sta <$> arg)
                     , app "Str"    (Str <$> arg)
                     , app "Ajs"    (Ajs <$> arg)
                     , app "Add"    (pure Add)
                     , app "Sub"    (pure Sub)
                     , app "Mul"    (pure Mul)
                     , app "Div"    (pure Div)
                     , app "Eq"     (pure Eq)
                     , app "Lt"     (pure Lt)
                     , app "Gt"     (pure Gt)
                     , app "Bra"    (Bra <$> arg)
                     , app "Brf"    (Brf <$> arg)
                     , app "Jsr"    (pure Jsr)
                     , app "Ret"    (pure Ret)
                     , app "Nop"    (pure Nop)
                     , app "Trap"   (Trap <$> arg)
                     , app "Halt"   (pure Halt)
                     , app "Label"  (Label <$> arg)
                     , app "Annote" (Annote <$> arg <*> arg <*> arg <*> arg <*> arg)
                     ]

instance Printable Instruction where
  pp (Ldc c)      = indent 4 (text "ldc" >#< showable c)
  pp (LdcL l)     = indent 4 (text "ldc" >#< ppLabel l)
  pp (Lds i)      = indent 4 (text "lds" >#< showable i)
  pp (Ldl i)      = indent 4 (text "ldl" >#< showable i)
  pp (Lda i)      = indent 4 (text "lda" >#< showable i)
  pp (Ldr r)      = indent 4 (text "ldr" >#< pp r)
  pp (Ldrr r1 r2) = indent 4 (text "ldrr" >#< pp r1 >#< pp r2)
  pp (Sts i)      = indent 4 (text "sts" >#< showable i)
  pp (Stl i)      = indent 4 (text "stl" >#< showable i)
  pp (Sta i)      = indent 4 (text "sta" >#< showable i)
  pp (Str r)      = indent 4 (text "str" >#< pp r)
  pp (Ajs i)      = indent 4 (text "ajs" >#< showable i)
  pp Add          = indent 4 (text "add")
  pp Sub          = indent 4 (text "sub")
  pp Mul          = indent 4 (text "mul")
  pp Div          = indent 4 (text "div")
  pp Eq           = indent 4 (text "eq")
  pp Lt           = indent 4 (text "lt")
  pp Gt           = indent 4 (text "gt")
  pp (Bra l)      = indent 4 (text "bra" >#< ppLabel l)
  pp (Brf l)      = indent 4 (text "brf" >#< ppLabel l)
  pp Jsr          = indent 4 (text "jsr")
  pp Ret          = indent 4 (text "ret")
  pp Nop          = indent 4 (text "nop")
  pp (Trap c)     = indent 4 (text "trap" >#< showable c)
  pp Halt         = indent 4 (text "halt")
  pp (Annote r l h c i)
                  = indent 4 (text "annote" >#< pp r >#< showable l >#< showable h >#< text c >#< showable i)
  pp (Label l)    = ppLabel l >|< colon

-- | Pretty prints a label.
ppLabel :: Label -> Doc
ppLabel l = text "L" >|< showable l

-- | Type of SSM code.
newtype Code = Code [Instruction]

instance Tree Code where
  fromTree (Code instrs) = fromTree instrs
  toTree                 = fmap Code . toTree

instance Printable Code where
  pp (Code instrs) = above [pp instr | instr <- instrs]

-------------------------------------------------------------------------------
-- Support for code generators
-------------------------------------------------------------------------------

-- | Accumulator type for 'Instruction's.
type CodeS = [Instruction] -> [Instruction]

-- | 'CodeS'-constructor for 'Ldc'.
ldc :: Const -> CodeS
ldc c = (Ldc c :)

-- | 'CodeS'-constructor for 'LdcL'.
ldcL :: Label -> CodeS
ldcL l = (LdcL l :)

-- | 'CodeS'-constructor for 'Lds'.
lds :: Offset -> CodeS
lds i = (Lds i :)

-- | 'CodeS'-constructor for 'Ldl'.
ldl :: Offset -> CodeS
ldl i = (Ldl i :)

-- | 'CodeS'-constructor for 'Lda'.
lda :: Offset -> CodeS
lda i = (Lda i :)

-- | 'CodeS'-constructor for 'Ldr'.
ldr :: Register -> CodeS
ldr r = (Ldr r :)

-- | 'CodeS'-constructor for 'Ldrr'.
ldrr :: Register -> Register -> CodeS
ldrr r1 r2 = (Ldrr r1 r2 :)

-- | 'CodeS'-constructor for 'Sts'.
sts :: Offset -> CodeS
sts i = (Sts i :)

-- | 'CodeS'-constructor for 'Stl'.
stl :: Offset -> CodeS
stl i = (Stl i :)

-- | 'CodeS'-constructor for 'Sta'.
sta :: Offset -> CodeS
sta i = (Sta i :)

-- | 'CodeS'-constructor for 'Str'.
str :: Register -> CodeS
str r = (Str r :)

-- | 'CodeS'-constructor for 'Ajs'.
ajs :: Offset -> CodeS
ajs i = (Ajs i :)

-- | 'CodeS'-constructor for 'Add'.
add :: CodeS
add = (Add :)

-- | 'CodeS'-constructor for 'Sub'.
sub :: CodeS
sub = (Sub :)

-- | 'CodeS'-constructor for 'Mul'.
mul :: CodeS
mul = (Mul :)

-- | 'CodeS'-constructor for 'Div'.
div :: CodeS
div = (Div :)

-- | 'CodeS'-constructor for 'Eq'.
eq :: CodeS
eq = (Eq :)

-- | 'CodeS'-constructor for 'Lt'.
lt :: CodeS
lt = (Lt :)

-- | 'CodeS'-constructor for 'Gt'.
gt :: CodeS
gt = (Gt :)

-- | 'CodeS'-constructor for 'Bra'.
bra :: Label -> CodeS
bra l = (Bra l :)

-- | 'CodeS'-constructor for 'Brf'.
brf :: Label -> CodeS
brf l = (Brf l :)

-- | 'CodeS'-constructor for 'Jsr'.
jsr :: CodeS
jsr = (Jsr :)

-- | 'CodeS'-constructor for 'Ret'.
ret :: CodeS
ret = (Ret :)

-- | 'CodeS'-constructor for 'Nop'.
nop :: CodeS
nop = (Nop :)

-- | 'CodeS'-constructor for 'Trap'.
trap :: Const -> CodeS
trap c = (Trap c :)

-- | 'CodeS'-constructor for 'Halt'.
halt :: CodeS
halt = (Halt :)

-- | 'CodeS'-constructor for 'Annote'.
annote :: Register -> Offset -> Offset -> String -> String -> CodeS
annote reg lo hi col info = (Annote reg lo hi col info :)

-- | 'CodeS'-constructor for 'Label'.
label :: Label -> CodeS
label l []                    = [Label l, Nop]
label l instrs@(Label l' : _) = Label l : Nop : instrs
label l instrs                = Label l : instrs
