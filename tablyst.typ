#import "@preview/cetz:0.4.2"
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "@preview/t4t:0.4.3": assert, get, test, is-none

/// One row in the proof table. 
///
/// - args (arguments):
///  - The following arguments are available:
///  - ctx (dictionary): New (added) proof context
///  - goal (content): The goal to be proven
///  - rule (string | array | dictionary): Name of the used proof rule, with optional arguments
///  - qed (bool): Whether this step completes the (sub)proof
/// -> dictionary
#let proofstep(..args) = {
  let args = get.args(args)(ctx: (:), "goal", rule: none, qed: false)

  let errors = ()

  if type(args.ctx) != dictionary {
    errors += "Proof step context must be a dictionary"
    args.ctx = (:)
  }
  if type(args.rule) not in (type(none), str, array, dictionary) {
    errors += "Proof step rule must be a string, array, or dictionary"
    args.rule = none
  }

  if type(args.rule) == str {
    args.rule = (name: args.rule, assumptions: ())
  } else if type(args.rule) == array {
    if args.rule.len() == 0 {
      errors += "Proof rules must not be an empty array"
      args.rule = none
    } else {
      args.rule = (name: args.rule.at(0), assumptions: args.rule.slice(1))
    }
  } else if type(args.rule) == dictionary {
    if args.rule.keys().len() != 1 {
      errors += "Can only apply exactly one proof rule at once"
      args.rule = none
    } else {
      let (rule-name, rule-args) = args.rule.pairs().first()
      if type(rule-args) != array {
        rule-args = (rule-args,)
      }
      args.rule = (name: rule-name, assumptions: rule-args)
    }
  }

  if type(args.qed) != bool {
    errors += "The `qed` argument must be a bool"
  }

  (type: "proofstep", errors: errors, ..args)
}

/// Create a subproof. Same syntax as `prooftable`.
#let subproof(..args) = {
  return (type: "subproof", args: args)
}

/// Draws a proof table diagram.
///
/// - proof-rules (dictionary): A list of proof rule definitions
/// - args (arguments): A list of invocations of `proofstep` and/or `subproof`
/// -> content
#let prooftable(proof-rules: none, ..args) = {
  let error(message) = footnote(
    numbering: (i) => text(fill: red, weight: "bold", [E#i#h(2pt)]),
    [#text(fill: red)[#message]]
  )
  let plural(count, word) = {
    str(count) + " " + word + if count != 1 { "s" } else { }
  }

  let format-assumption = (name, def: none) => {
    $mono(#name)$;
    if def != none {
      math.space
      $: def $
    }
  }

  let validate-step(ctx, goal, rule, qed) = {
    if rule == none {
      return ()
    }

    let (name, assumptions) = rule
    let errors = ()

    let known-rule = proof-rules.at(name, default: none)
    if known-rule == none {
      errors.push[Unknown proof rule #smallcaps(name)]
      known-rule = (:)
    } else if assumptions.len() != known-rule.assumptions {
      errors.push[
        The proof rule #smallcaps(name) expects #plural(known-rule.assumptions, "assumption")
        but received #plural(assumptions.len(), "assumption") (#{ assumptions.map(format-assumption).join[, ] })
      ]
    }

    if "goalRequirement" in known-rule.keys() {
      if known-rule.goalRequirement not in get.text(goal) {
        errors.push[
          The proof rule #smallcaps(name) requires the goal #goal
          to contain the symbol $#known-rule.goalRequirement$
        ]
      }
    }
    for assumption in assumptions {
      if assumption not in ctx.keys() {
        errors.push[Tried to use undefined assumption #format-assumption(assumption)]
      }
      if "requireGoalAndAssumptionEqual" in known-rule.keys() {
        if get.text(goal) != get.text(ctx.at(assumption, default: [])) {
          errors.push[
            The proof rule #smallcaps(name) requires
            the assumption #format-assumption(assumption, def: ctx.at(assumption, default: none))
            and the goal #goal to match
          ]
        }
      }
      if "assumptionRequirement" in known-rule.keys() {
        if known-rule.assumptionRequirement not in get.text(ctx.at(assumption, default: "")) {
          errors.push[
            The proof rule #smallcaps(name) requires
            the assumption #format-assumption(assumption, def: ctx.at(assumption, default: none))
            to contain the symbol $#known-rule.assumptionRequirement$
          ]
        }
      }
    }

    let expected-qed = known-rule.at("qed", default: false)
    if qed != expected-qed {
      errors.push[
        `qed` should be #expected-qed, but is #qed
      ]
    }

    return errors
  }

  let validate-tree(ctx: (:), tree) = {
    if proof-rules == none {
      return tree
    }

    let steps = ()
    for step in tree.steps {
      step.errors = ()
      for assumption in step.ctx.keys() {
        if assumption in ctx.keys() {
          step.errors.push[
            Tried to redefine already defined assumption #format-assumption(assumption)
          ]
        }
      }
      ctx += step.ctx
      step.errors += validate-step(ctx, step.goal, step.rule, step.qed)
      steps.push(step)
    }

    tree.children = tree.children.map(child => validate-tree(ctx: ctx, child))

    return (..tree, steps: steps)
  }

  let format-rule(rule) = {
    smallcaps(rule.name)
    for assumption in rule.assumptions {
      " "
      format-assumption(assumption)
    }
  }

  let prooftable-build-table(steps) = {
    let stroke = 0.5pt + black

    let rows = (table.header(..([Context], [Goal], [Rule]).map(align.with(center))),)
    let qedRows = (false,)

    for step in steps {
      let ctx = step.ctx.pairs().map(((name, def)) => {
        format-assumption(name, def: def)
      }).join(linebreak())
      let goal = align(center, step.goal)
      let rule = {
        if is-none(step.rule) {
          []
        } else {
          format-rule(step.rule)
        }
        if step.errors.len() > 0 {
          step.errors.map(error).join[]
        }
      }
      rows.push((ctx, goal, rule));
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

  let prooftable-parse-args(..args) = {
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
          if "goal" not in arg.keys() {
            arg.goal = []
          }
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

  let prooftable-draw-cetz-tree(tree) = {
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

  let prooftable-draw-fletcher-tree(tree, ..args) = {
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
          x: tree.pos.x + (i / (child-count - 1)) * available-breadth - (available-breadth / 2),
          y: tree.pos.y + 1,
        )
      })
      tree
    }
    let make-fletcher-node(tree, name: "prooftable-node-0") = {
      let debug = args.named().at("debug", default: false)
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

    tree = annotate-tree(tree)

    let config = (:)
    if "spacing" in args.named().keys() {
      config += (spacing: args.named().spacing)
    } else if "debug" in args.named().keys() {
      config += (debug: args.named().debug)
    }
    
    align(center, diagram(
      make-fletcher-node(tree),
      ..config
    ))
  }

  let tree = prooftable-parse-args(..args)
  tree = validate-tree(tree)
  return [ #prooftable-draw-fletcher-tree(tree, ..args) ]
}
