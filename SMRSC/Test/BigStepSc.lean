--
-- SMRSC.Tests.BigStepSc
--

import Batteries
import Aesop

import SMRSC.Util
import SMRSC.Graphs
import SMRSC.BarWhistles
import SMRSC.BigStepSc

-- ScWorld Conf3

-- This is a silly world with 3 possible configurations.
-- (Just for testing.)

inductive Conf3 : Type where
  | C0 : Conf3
  | C1 : Conf3
  | C2 : Conf3
deriving DecidableEq, Repr

open Conf3

def conf3_drive : Conf3 -> List Conf3
  | C0 => [C1, C2]
  | C1 => [C0]
  | C2 => [C1]

def conf3_rebuildings : Conf3 -> List Conf3
  | C0 => [C1]
  | _  => []

def Sc3 : ScWorld Conf3 :=
  let develop (c : Conf3) : List (List Conf3) :=
    [ conf3_drive c ] ++ List.map (· :: []) (conf3_rebuildings c)
  ⟨ (· = ·), decEq, develop⟩

-- NDSC

open Graph LazyGraph NDSC NDSC_PW

open List.Mem (head tail)

theorem w3graph1 : NDSC (s := Sc3) [] C0 $
  forth C0 [
    forth C1 [ back C0 ],
    forth C2 [ forth C1 [ back C0 ] ]]
:=
  build (nomatch ·) (head _)
    (cons (build (nomatch ·) (head _)
    (cons (fold (.inr (.inl (by rfl)))) nil))
    (cons (build (nomatch ·) (head _)
    (cons (build (nomatch ·) (head _)
    (cons (fold (.inr (.inr (.inl rfl)))) nil)) nil)) nil))

def w3graph2 : NDSC (s := Sc3) [] C0 $
  forth C0 [ forth C1 [ back C0 ]]
:=
  build (nomatch ·) (tail _ (head _))
    (cons (build (nomatch ·) (head _)
    (cons (fold (.inr (.inl rfl))) nil)) nil)

def Plw4 : BarWhistle Conf3
  := pathLengthWhistle Conf3 4

#guard naive_mrsc Sc3 Plw4 C0 == [
  forth C0 [
    forth C1 [back C0],
    forth C2 [forth C1 [back C0]]],
    forth C0 [forth C1 [back C0]]]

#guard (lazy_mrsc Sc3 Plw4 C0 : LazyGraph Conf3) ==
  build C0 [
    [
      build C1 [[stop C0]],
      build C2 [[build C1 [[stop C0]]]]],
    [
      build C1 [[stop C0]]]]
