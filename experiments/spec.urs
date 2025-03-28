module spec where

def Spectrum : U∞ := Spectrum

-- Constructors
def deloop (E : Spectrum) (k : Nat) : Grpd (∞ - k) := Ω^k E
def stable-eq (E E' : Spectrum) (φ : E → Ω E') : E ≃ Ω E' := φ

-- Eliminators
def loop (E : Spectrum) (e : E) : Ω E := loop e
def stabilize (E : Spectrum) : Maps E (Ω^∞ E_∞) := stabilize E

-- Computation rules
def loop-β (E : Spectrum) (e : E)
  : Path (Ω E) (loop E e) (loop E e) := idp (Ω E) (loop e)
