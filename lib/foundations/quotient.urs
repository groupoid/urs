module quotient where

import foundations.smooth
import foundations.groupoid

-- Define the equivalence relation induced by a local G-action
def g-action-rel (G : Grpd 1) (X : SmthSet) (act : G → X → X) : X → X → Type
  := λ x y, Σ (g : G), Path X (act g x) y

-- Quotient X by the G-action
def g-quotient (G : Grpd 1) (X : SmthSet) (act : G → X → X) : Type
  := Quotient X (g-action-rel G X act)

-- Introduction: Map x to its equivalence class
def g-quotient-intro (G : Grpd 1) (X : SmthSet) (act : G → X → X) (x : X) : g-quotient G X act
  := Quot X (g-action-rel G X act) x

-- Elimination: Lift a function respecting the G-action
def g-quotient-lift (G : Grpd 1) (X : SmthSet) (act : G → X → X) 
    (B : Type) (f : X → B) 
    (h : Π (x : X) (y : X), (g-action-rel G X act) x y → Path B (f x) (f y))
    : g-quotient G X act → B
  := QuotLift X (g-action-rel G X act) B f h