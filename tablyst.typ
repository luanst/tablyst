#import "@preview/cetz:0.4.2"
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#let error(message) = footnote(
  numbering: (i) => text(fill: red, weight: "bold", [E#i#h(2pt)]),
  [#text(fill: red)[#message]]
)
#let plural(count, str) = [#count #str#if count != 1 [s]]

#let assumptionState = state("assumptions", (:))
#let goalState = state("goals", ())
#let prooftableCounter = counter("prooftable")

#let format-assumption(name, def: none, display-only: false) = {
  $sans(#name)$;
  if def != none {
    context if not display-only {
      let prooftableIdx = str(prooftableCounter.get().at(0));
      if name in assumptionState.get().at(prooftableIdx, default: (:)).keys() {
        error[Tried to redefine assumption #format-assumption(name).]
      }
      assumptionState.update(assumptions => {
        if not assumptions.keys().contains(prooftableIdx) {
          assumptions.insert(str(prooftableIdx), (:))
        }
        assumptions.at(str(prooftableIdx)).insert(name, def)
        assumptions
      })
    }
    math.space
    $: def $
  }
}

#let validate-rule(..rule) = {
  // TODO: add qed validation
  let knownRules = (
    AndElim: (assumptions: 1, assumptionRequirement: "∧"),
    AndIntro: (assumptions: 0, goalRequirement: "∧"),
    OrElim: (assumptions: 1, assumptionRequirement: "∨"),
    OrIntro: (assumptions: 0, goalRequirement: "∨"),
    Assumption: (assumptions: 1, requireGoalAndAssumptionEqual: true),
    ImplIntro: (assumptions: 0, goalRequirement: "→"),
  )

  let name = rule.at(0, default: "")

  let assumptions = rule.pos().slice(1)
  if assumptions.len() == 1 and type(assumptions.at(0)) == array {
    assumptions = assumptions.at(0)
  }
  
  let errors = context {
    let knownRule = knownRules.at(name, default: none)
    if name == "" {
      return
    } else if knownRule == none {
      error[Unknown rule #smallcaps(name).]
      return
    } else if assumptions.len() != knownRule.assumptions {
      error[
        Rule #smallcaps(name) expects #plural(knownRule.assumptions, "assumption"),
        but received #plural(assumptions.len(), "assumption") (#assumptions.map(it => format-assumption(it)).join([, ])).
      ]
    }

    let prooftableIdx = prooftableCounter.get().at(0);
    let knownAssumptions = assumptionState.get().at(str(prooftableIdx), default: (:))
    let goal = goalState.get().last()

    // TODO: this depends on repr :(
    if "goalRequirement" in knownRule.keys() {
      if not repr(goal.fields().body).contains("[" + knownRule.goalRequirement + "]") {
        error[The rule #smallcaps(name) requires the goal $goal$ to contain the symbol $#knownRule.goalRequirement$.]
      }
    }
    for assumption in assumptions {
      if not assumption in knownAssumptions.keys() {
        error[Tried to use undefined assumption #format-assumption(assumption).]
      } else if "requireGoalAndAssumptionEqual" in knownRule.keys() {
        if not repr(goal.fields().body) == repr(knownAssumptions.at(assumption).fields().body) {
          error[
            The rule #smallcaps(name) requires assumption
            #format-assumption(assumption, def: knownAssumptions.at(assumption), display-only: true)
            and goal $goal$ to match.
          ]
        }
      } else if "assumptionRequirement" in knownRule.keys() {
        if not repr(knownAssumptions.at(assumption).fields().body).contains("[" + knownRule.assumptionRequirement + "]") {
          error[
            The rule #smallcaps(name) requires the assumption
            #format-assumption(assumption, def: knownAssumptions.at(assumption), display-only: true)
            to contain the symbol $#knownRule.assumptionRequirement$.
          ]
        }
      }
    }
  }
  
  return (name: name, assumptions: assumptions, errors: errors)
}

#let format-rule(..rule) = {
  let rule = validate-rule(..rule)
  smallcaps(rule.name);
  for assumption in rule.assumptions {
    " ";
    format-assumption(assumption)
  }
  rule.errors
}

#let proofstep-internal(ctx, goal, rule, qed) = {
  let ctx = {
    if type(ctx) == array {
      for assumption in ctx {
        if type(assumption) == array {
          format-assumption(assumption.at(0), def: assumption.at(1))
        } else if type(assumption) == dictionary {
          assumption.pairs().map(it => {
            format-assumption(it.at(0), def: it.at(1))
          }).join(linebreak())
        } else {
          format-assumption(assumption)
        }
        linebreak()
      }
    } else if type(ctx) == dictionary {
      ctx.pairs().map(it => {
        format-assumption(it.at(0), def: it.at(1))
      }).join(linebreak())
    } else {
      ctx
    }
  }
  let rule = {
    if type(rule) == str {
      format-rule(rule)
    } else if type(rule) == array {
      format-rule(..rule)
    } else if type(rule) == dictionary {
      rule.pairs().map(it => {
        format-rule(..it)
      }).join(linebreak())
    } else {
      rule
    }
  }
  (type: "proofstep", row: (ctx, align(center, goal), rule), qed: qed)
}

#let proofstep(..args) = {
  let pos-arg = 0

  let qed = if args.named().keys().contains("qed") {
    args.named().at("qed")
  } else {
    false
  }

  let rule = if args.named().keys().contains("rule") {
    args.named().at("rule")
  } else if args.pos().len() > pos-arg {
    pos-arg += 1
    args.pos().at(args.pos().len() - pos-arg)
  } else {
    ""
  }
  
  let goal = if args.named().keys().contains("goal") {
    args.named().at("goal")
  } else if args.pos().len() > pos-arg {
    pos-arg += 1;
    args.pos().at(args.pos().len() - pos-arg)
  } else {
    $$
  }
  let stateUpdate = goalState.update(it => {
    it.push(goal)
    it
  })
  
  let ctx = if args.named().keys().contains("ctx") {
    args.named().at("ctx")
  } else if args.pos().len() > pos-arg {
    pos-arg += 1;
    args.pos().at(args.pos().len() - pos-arg)
  } else {
    none
  }

  proofstep-internal(ctx, goal + stateUpdate, rule, qed)
}

#let subproof(..args) = {
  return (type: "subproof", args: args)
}

#let prooftable-build-table(steps) = {
  let stroke = 0.5pt + black

  let rows = (table.header(..([Context], [Goal], [Rule]).map(align.with(center))),)
  let qedRows = (false,)
  for step in steps {
    rows.push(step.row);
    qedRows.push(false);
    if step.qed {
      rows.push(table.hline(stroke: stroke))
      rows.push(([], [], []))
      qedRows.push(true)
    }
  }

  return table(
    columns: 3,
    rows: qedRows.map(it => if it { 2pt } else { auto }),
    align: horizon + left,
    stroke: (x, y) => (
      top: none,
      bottom: stroke,
      left: none,
      right: if x < 2 and not qedRows.at(y) { stroke } else { none }
    ),
    ..rows.flatten()
  )

  mainTable
}

#let prooftable-parse-args(..args) = {
  (
    // TODO: sanitize args
    pos: args.at("pos", default: (:)),
    shift: args.at("shift", default: (x: 0, y: 0)),
  ) + args.pos().fold(
    (steps: (), children: (), errors: []),
    (acc, arg) => {
      if type(arg) != dictionary or "type" not in arg.keys() {
        acc.errors += error[Invalid proof table argument #linebreak() #arg]
      } else if arg.type == "proofstep" {
        acc.steps.push(arg)
      } else if arg.type == "subproof" {
        acc.children.push(prooftable-parse-args(..arg.args))
      } else {
        acc.errors += error[Unknown proof table element type #raw(arg.type).]
      }
      acc
    }
  )
}

#let prooftable-draw-cetz-tree(tree) = {
    let to-cetz-tree(tree) = {
      (prooftable-build-table(tree.steps),) + tree.children.map(to-cetz-tree)
    }
    align(center, 
      cetz.canvas({
        import cetz.draw: *
        set-style(stroke: 0.7pt, mark: (end: "straight"))
        cetz.tree.tree(to-cetz-tree(tree), grow: 0)
      })
    )
    tree.errors
}

#let prooftable-draw-fletcher-tree(tree, ..args) = {
  let tree-breadth(tree) = {
    1 + tree.children.map(tree-breadth).sum(default: 0)
  }
  let stretch = args.named().at("stretch", default: 1)
  let annotate-tree(tree, available-breadth: stretch, x: stretch / 2, y: 0) = {
    tree.pos = (
      x: (tree.pos.at("x", default: x) + tree.shift.x),
      y: (tree.pos.at("y", default: y) + tree.shift.y),
    )
    let child-count = tree.children.len()
    tree.children = tree.children.enumerate().map(((i, child)) => {
      annotate-tree(
        child,
        available-breadth: available-breadth / child-count,
        // x: x + (i - (child-count - 1) / 2) * (available-breadth / child-count),
        x: tree.pos.x + (i / (child-count - 1)) * available-breadth - (available-breadth / 2),
        y: tree.pos.y + 1,
      )
    })
    tree
  }
  let make-fletcher-node(tree, name: "prooftable-node-0") = {
    let debug = args.named().at("debug", default: false)
    // let debug = args.named().at("debug", default: true)
    let node-options = (
      name: label(name),
      shape: "rect",
    )
    if debug {
      node-options += (fill: yellow)
    }
    node((tree.pos.x, tree.pos.y), prooftable-build-table(tree.steps), ..node-options)
    if debug {
      node((tree.pos.x, tree.pos.y), $(#tree.pos.x, space #tree.pos.y)$, fill: red)
    }
    for (i, child) in tree.children.enumerate().rev() {
      let child-name = name + "-" + str(i)
      make-fletcher-node(child, name: child-name)
      edge(vertices: (label(name), label(child-name)), "->")
    }
  }

  tree.errors
  tree = annotate-tree(tree)

  let config = (:)
  if "spacing" in args.named().keys() {
    config += (spacing: args.named().spacing)
  } else if "debug" in args.named().keys() {
    config += (debug: args.named().debug)
  }
  
  align(center, diagram(
    make-fletcher-node(tree),
    // spacing: args.named().at("spacing", auto)
    ..config
  ))
}

#let prooftable(..args) = {
  let tree = prooftable-parse-args(..args)
  prooftable-draw-fletcher-tree(tree, ..args)
  prooftableCounter.step()
}

#prooftable(
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
  proofstep($P and Q -> Q and P$, "ImplIntro"),
  proofstep((H1: $P and Q$), $Q and P$, (AndElim: "H1")),
  proofstep((H2: $P$, H3: $Q$), $Q and P$, "AndIntro"),
  subproof(proofstep($Q$, (Assumption: "H3"), qed: true)),
  subproof(proofstep($P$, (Assumption: "H2"), qed: true)),
)

#v(1fr)

#prooftable(
  proofstep($P or Q <- Q or P$, (ImplIntro: "H1")),
  proofstep((H1: $P or Q$), $Q or P$, (AndElim: "H1")),
  proofstep((H1: $P$, H2: $Q$), $Q or P$, "AndIntro"),
  subproof(proofstep($R$, (Assumption: "H2"), qed: true)),
  subproof(proofstep($P$, (Assumption: "H3"), qed: true)),
)

#pagebreak()

#prooftable(
  // spacing: (-80pt, 40pt),
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
      proofstep($Q$, (Assumption: "H3"), qed: true)
    ),
    subproof(
      shift: (x: 0.45, y: 0.5),
      proofstep($Q$, (Assumption: "H3"), qed: true)
    ),
  ),
  // debug: true,
)

#pagebreak()

#prooftable(
  spacing: (-5pt, 30pt),
  pos: (x: 1.5, y: 0),
  proofstep(goal: $(P or P and Q) -> Q and P$, rule: "ImplIntro"),
  proofstep(ctx: (H1: $P or Q and P$), goal: $Q and P$, rule: (OrElim: "H1")),
  subproof(
    pos: (x: 0.5, y: 1),
    proofstep(ctx: (H2: $P$), goal: $Q and P$, rule: "AndIntro"),
    subproof(
      pos: (x: 0, y: 2),
      proofstep(goal: $Q$, rule: (Assumption: "H5"), qed: true),
    ),
    subproof(
      pos: (x: 1, y: 2),
      proofstep(goal: $P$, rule: (Assumption: "H2"), qed: true),
    ),
  ),
  subproof(
    pos: (x: 2, y: 1.2),
    proofstep(ctx: (H3: $P and Q$), goal: $Q and P$, rule: ("AndElim", "H3")),
    proofstep(ctx: (H4: $P$, H5: $Q$), goal: $Q and P$, rule: "AndIntro"),
    subproof(
      pos: (x: 1.2, y: 3),
      proofstep(goal: $Q$, rule: (Assumption: "H5"), qed: true),
    ),
    subproof(
      pos: (x: 2.3, y: 3),
      proofstep(goal: $P$, rule: (Assumption: "H4"), qed: true),
    ),
  ),
)
#pagebreak()

#prooftable(
  stretch: 1.5,
  // debug: true,
  proofstep(goal: $(P or P and Q) -> Q and P$, rule: "ImplIntro"),
  proofstep(ctx: (H1: $P or Q and P$), goal: $Q and P$, rule: (OrElim: "H1")),
  subproof(
    proofstep(ctx: (H2: $P$), goal: $Q and P$, rule: "AndIntro"),
    subproof(
      shift: (x: -0.2, y: 0),
      // FIXME: this should throw an error
      proofstep(goal: $Q$, rule: (Assumption: "H5"), qed: true),
    ),
    subproof(
      shift: (x: 0, y: 0),
      proofstep(goal: $P$, rule: (Assumption: "H2"), qed: true),
    ),
  ),
  subproof(
    shift: (x: -0.2, y: 1),
    proofstep(ctx: (H3: $P and Q$), goal: $Q and P$, rule: ("AndElim", "H3")),
    proofstep(ctx: (H4: $P$, H5: $Q$), goal: $Q and P$, rule: "AndIntro"),
    subproof(
      shift: (x: -0.4, y: 0),
      proofstep(goal: $Q$, rule: (Assumption: "H5"), qed: true),
    ),
    subproof(
      shift: (x: -0.2, y: 0),
      proofstep(goal: $P$, rule: (Assumption: "H4"), qed: true),
    ),
  ),
)
