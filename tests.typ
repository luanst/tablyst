#import "tablyst.typ": prooftable, proofstep, subproof

#let proof-rules = (
  AndElim: (assumptions: 1, assumptionRequirement: "∧"),
  AndIntro: (assumptions: 0, goalRequirement: "∧"),
  OrElim: (assumptions: 1, assumptionRequirement: "∨"),
  OrIntro1: (assumptions: 0, goalRequirement: "∨"),
  OrIntro2: (assumptions: 0, goalRequirement: "∨"),
  Assumption: (assumptions: 1, requireGoalAndAssumptionEqual: true, qed: true),
  ImplIntro: (assumptions: 0, goalRequirement: "→"),
)
#let prooftable = (..args) => prooftable(proof-rules: proof-rules, ..args)

#prooftable(
  proofstep(goal: $x = 7$),
  proofstep(goal: $P and Q -> Q and P$, rule: "ImplIntro"),
  proofstep(ctx: (H1: $P and Q$), goal: $Q and P$, rule: (AndElim: "H1")),
  proofstep(ctx: (H2: $P$, H3: $Q$), goal: $Q and P$, rule: "AndIntro"),
  subproof(
    proofstep(goal: $Q$, rule: (Assumption: "H3"), qed: true),
  ),
  subproof(
    proofstep(goal: $P$, rule: (Assumption: "H2"), qed: true),
  ),
)

#v(1fr)

#prooftable(
  proofstep(goal: $P or Q <- Q or P$, rule: (ImplIntro: "H1")),
  proofstep(ctx: (H1: $P or Q$), goal: $Q or P$, rule: (AndElim: "H1")),
  proofstep(ctx: (H1: $P$, H2: $Q$), goal: $Q or P$, rule: "AndIntro"),
  subproof(proofstep(goal: $R$, rule: (Assumption: "H2"), qed: true)),
  subproof(proofstep(goal: $P$, rule: (Assumption: "H3"), qed: true)),
)

#pagebreak()

#prooftable(
  proofstep(goal: $P or Q -> Q or P$, rule: "ImplIntro"),
  proofstep(ctx: (H1: $P or Q$), goal: $Q and P$, rule: (AndElim: "H1")),
  proofstep(ctx: (H1: $P$, H2: $Q$), goal: $Q and P$, rule: "AndIntro"),
  subproof(proofstep(goal: $Q$, rule: (Assumption: "H2"), qed: true)),
  subproof(proofstep(goal: $P$, rule: (Assumption: "H1"), qed: true)),
)

#pagebreak()

#prooftable(
  proofstep(goal: $P and Q -> Q and P$, rule: "ImplIntro"),
  proofstep(ctx: (H1: $P and Q$), goal: $Q and P$, rule: (AndElim: "H1")),
  proofstep(ctx: (H2: $P$, H3: $Q$), goal: $Q and P$, rule: "AndIntro"),
  subproof(
    proofstep(goal: $Q$, rule: (Assumption: "H3")),
    proofstep(goal: $Q$, rule: (Assumption: "H3"), qed: true),
    proofstep(goal: $Q$, rule: (Assumption: "H3")),
    subproof(
      shift: (x: -0.3, y: 0),
      proofstep(goal: $A$),
      proofstep(goal: $B$),
      proofstep(goal: $C$, qed: true),
    ),
    subproof(
      shift: (x: -0.1, y: 0),
      proofstep(goal: $A$),
      proofstep(goal: $B$),
      proofstep(goal: $C$, qed: true),
    ),
  ),
  subproof(
    proofstep(goal: $P$, rule: (Assumption: "H2"), qed: true),
    subproof(
      proofstep(goal: $A$),
      proofstep(goal: $B$),
      proofstep(goal: $C$, qed: true),
    ),
    subproof(
      shift: (x: 0.2, y: 1),
      proofstep(goal: $Q$, rule: (Assumption: "H3"), qed: true)
    ),
    subproof(
      shift: (x: 0.45, y: 0.5),
      proofstep(goal: $Q$, rule: (Assumption: "H3"), qed: true)
    ),
  ),
  // debug: true,
)

#pagebreak()

#prooftable(
  stretch: 1.5,
  // debug: true,
  proofstep(goal: $(P or P and Q) <- Q and P$, rule: "ImplIntro"),
  proofstep(ctx: (H1: $P or Q space amp space P$), goal: $Q and P$, rule: (AndElim: "H1")),
  subproof(
    proofstep(ctx: (H2: $P$), goal: $Q and P$, rule: "OrIntro"),
    subproof(
      shift: (x: 0, y: 0.4),
      proofstep(goal: $Q$, rule: (Assumption: "H5"), qed: true),
    ),
    subproof(
      shift: (x: 0, y: -0.2),
      proofstep(goal: $P$, rule: (Assumption: "H3")),
    ),
  ),
  subproof(
    shift: (x: -0.2, y: 0.5),
    proofstep(ctx: (H3: $P and Q$), goal: $Q and P$, rule: ("OrElim", "H3")),
    proofstep(ctx: (H4: $P$, H5: $Q$), goal: $Q and P$, rule: "OrIntro1"),
    subproof(
      shift: (x: -0.4, y: 0.5),
      proofstep(goal: $Q$, rule: (Assumption: "H2"), qed: true),
    ),
    subproof(
      shift: (x: -0.2, y: 0.5),
      proofstep(goal: $P$, rule: (Assumption: "H4"), qed: true),
    ),
  ),
)

#pagebreak()

#prooftable(
  // debug: true,
  proofstep(goal: $(P or P and Q) -> Q or P$, rule: "ImplIntro"),
  proofstep(ctx: (H1: $P or P and Q$), goal: $Q or P$, rule: (OrElim: "H1")),
  subproof(
    proofstep(ctx: (H2: $P$), goal: $Q or P$, rule: "OrIntro2"),
    proofstep(goal: $P$, rule: (Assumption: "H2"), qed: true),
  ),
  subproof(
    proofstep(ctx: (H3: $P and Q$), goal: $Q and P$, rule: ("AndElim", "H3")),
    proofstep(ctx: (H4: $P$, H5: $Q$), goal: $Q and P$, rule: "AndIntro"),
    subproof(
      shift: (x: -0.2, y: 0),
      proofstep(goal: $Q$, rule: (Assumption: "H5"), qed: true),
    ),
    subproof(
      shift: (x: 0.2, y: 0),
      proofstep(goal: $P$, rule: (Assumption: "H4"), qed: true),
    ),
  ),
)