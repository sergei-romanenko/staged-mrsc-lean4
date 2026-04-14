--
-- SMRSC.Util
--

import Batteries
import Aesop

--
-- Implication reasoning
--

-- Reasoning by implication
-- Implication is a preorder relation...

def «⇒» (p q : Prop) : Prop :=
  p -> q

instance impTrans : Trans «⇒» «⇒» «⇒» where
  trans pq qr := qr ∘ pq

infixr:20 " ⇒ " => «⇒»
