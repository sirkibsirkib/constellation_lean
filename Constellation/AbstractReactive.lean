
class Sig2 where
  Fact: Type
  Effect: Type

variable [Sig2]

structure ReactiveRule: Type where
  cond: List Sig2.Fact
  post: Sig2.Effect

def trig_all
  (l: List ReactiveRule)
  (f: Sig2.Fact → Bool)
: List Sig2.Effect :=
  l |>.filter (·.cond.all f)
    |>.map ReactiveRule.post
