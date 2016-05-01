module NaiveRaft where
open import Prelude.Nat
open import Prelude.Fin 
open import Prelude.Vec 
open import Prelude.Bool
open import Prelude.Maybe
open import Prelude.String
open import Prelude.List 

record Entry : Set  where
 field 
--   eAt     :: Name
--  ,eClient :: EClientId -- should this be Name?
--  ,eId     :: ESeqNum
  Index  : Nat 
  Term   : Nat 
  Input  : String

data NodeSort : Set where
    Leader : NodeSort
    Follower : NodeSort
    Candidate :  NodeSort

record CommonNodeState : Set   where
   field
      ClusterSize : Nat
      NodeId : Fin ClusterSize  -- MY NAME 
      currentTerm : Nat
      votedForThisTerm : Maybe (Fin ClusterSize)
      leaderId : Maybe (Fin ClusterSize)

      maxCommittedLogIndex : Nat -- aka commitIndex
      commitedLog : Vec Entry maxCommittedLogIndex
      uncommitedLog : List Entry
      maxAppliedLogIndex  : Nat 
      -- if candidate, must vote for self + requestVoteRPC all the nodes

     
      
{-

    -- persistent
       currentTerm        :: Term
      ,votedFor           :: Maybe Name
      ,leaderId           :: Maybe Name
      ,log                :: [Entry input]
    -- volatile
      ,commitIndex        :: LogIndex
      ,lastApplied        :: LogIndex
      ,stateMachine       :: stateMachineData
-}

data SortSpecificState : NodeSort -> Set where




-- record NodeBehavior   : NodeSort ->  Set   where
   -- coinductive 
   --field
--      Timeout : forall s -> (SortSpecificState s) -> 





{-
record Candidate  : Set where
      coinductive
      field
        clusterSize : Nat 
        currentTerm : Nat
        nodeId : Fin clusterSize 
        votesReceived : Vec Bool clusterSize 
        timeout : Candidate
        elected : Leader 

record Follower  : Set where
      coinductive
      field
        clusterSize : Nat 
        currentTerm : Nat
        nodeId : Fin clusterSize 
        timeout : Candidate

record Leader   : Set where
      coinductive
      field
        clusterSize : Nat 
        currentTerm : Nat
        nodeId : Fin clusterSize 
        


   --        have : Food
   --     eat : Full
--open Candidate 
-}
