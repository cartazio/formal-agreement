module BasicEpaxos  where

open import Data.String using (String)
open import Data.String as Str
open import Data.Vec
open import Data.Nat  
open import Data.Bool
open import Level using (Level ; suc ; _⊔_ )
record OtherNode : Set where
       field 
          ndName : String
          

record ReplicaConfig : Set where
      constructor mkReplicaConf
      field
        uniqueName : String
      --  replicaCert : KeyPair uniqueName -- we're not dealing with this right now
        otherMembersCount : ℕ
        clusterMemberSet : Vec ( OtherNode ) otherMembersCount
          -- this 
          
--         totalSize 

      --- x.elemTy

data PathType : Set where
     Both : PathType
     SlowPath : PathType
     FastPath : PathType 

data StateFlavor : Set  where
           StateBoth : StateFlavor
           StateSlow : StateFlavor

-- 




-- this is the states of a "command leader"
data CmdState :  Set where
   AwaitingClientRequest : CmdState 
   SendingPreAccept : CmdState 
   UponReceivingPreAccepOKt≥⌊n/2⌋ : CmdState

data CmdTransition : CmdState -> CmdState -> Set where
  cmdID : ∀ {a} -> CmdTransition a a 
  cmdACR : CmdTransition AwaitingClientRequest SendingPreAccept 
  cmdSPA : CmdTransition SendingPreAccept  UponReceivingPreAccepOKt≥⌊n/2⌋
  cmdCompose : ∀ {a  c : CmdState } (b :  CmdState )   -> CmdTransition b c   ->  CmdTransition a b  -> CmdTransition a c  


bar  : ∀ ( a :  CmdState) { b  : CmdState}    ->  CmdTransition a b  ->  ℕ
bar AwaitingClientRequest cmdID = zero
bar AwaitingClientRequest cmdACR = zero
bar AwaitingClientRequest (cmdCompose b y y₁) = 1 + bar b y + bar AwaitingClientRequest y₁
bar SendingPreAccept cmdID = zero
bar SendingPreAccept cmdSPA = zero
bar SendingPreAccept (cmdCompose b y y₁) = 1 + bar b y + bar SendingPreAccept y₁
bar UponReceivingPreAccepOKt≥⌊n/2⌋ cmdID = zero
bar UponReceivingPreAccepOKt≥⌊n/2⌋ (cmdCompose b y y₁) = 1 + bar b y + bar  UponReceivingPreAccepOKt≥⌊n/2⌋ y₁

foo : ∀ ( a :  CmdState) { b  : CmdState}    ->  CmdTransition a b  ->  ℕ
foo AwaitingClientRequest cmdID = zero
foo AwaitingClientRequest cmdACR = zero
foo AwaitingClientRequest (cmdCompose b x y) = 1 +  foo AwaitingClientRequest y  + foo b x 
foo SendingPreAccept cmdID = zero
foo SendingPreAccept cmdSPA = zero
foo SendingPreAccept (cmdCompose b x x₁) =   1 + foo SendingPreAccept x₁ + foo b x 
foo UponReceivingPreAccepOKt≥⌊n/2⌋ cmdID = zero
foo UponReceivingPreAccepOKt≥⌊n/2⌋ (cmdCompose b y y₁) = 1 + foo b y + foo UponReceivingPreAccepOKt≥⌊n/2⌋ y₁
   
data CoordCmdTransitions : PathType -> Set where

