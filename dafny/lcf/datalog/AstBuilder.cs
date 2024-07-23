using System;
using System.Numerics;
using System.Collections.Generic;
using System.Linq;
using Antlr4.Runtime;
using _System;
using Dafny;

namespace _module
{
  internal class AstBuilder : datalogBaseVisitor<object>
  {
    public override object VisitTrace(datalogParser.TraceContext context) {
      var traceevents = new List<_module.Event>();
      foreach (var traceevent in context.traceevent()) {
        var dafny_event = (_module.Event)VisitTraceevent(traceevent);
        traceevents.Add(dafny_event);
      }
      return Sequence<_module.Event>.Create(traceevents.Count, i => traceevents[(int) i]);
    }

    public override object VisitTraceevent(datalogParser.TraceeventContext context) {
      var port = (_IPort) VisitPort(context.port());
      var level = (BigInteger) VisitInteger(context.level);
      var goal = (_IProp) VisitClause(context.goal);
      var id = (BigInteger) VisitInteger(context.id);
      var choice = (_IProp) VisitClause(context.choice);
      return new _module.Event(port, level, goal, id, choice);
    }

    public override object VisitPort(datalogParser.PortContext context) => context.name.Text switch {
      "call" => new Port_Call(),
      "redo" => new Port_Redo(),
      "unify" => new Port_Unify(),
      "exit" => new Port_Exit(),
      "fail" => new Port_Fail(),
      _ => throw new ArgumentOutOfRangeException("port", $"Unhandled port type {context.name.Text}"),
    };

    public override object VisitInteger(datalogParser.IntegerContext context) {
      return BigInteger.Parse(context.numeral.Text);
    }

    public override object VisitProgram(datalogParser.ProgramContext context) {
      var rules = new List<_module.Rule>();
      foreach (var fact in context.fact()) {
        var dafny_rule = (_module.Rule) VisitFact(fact);
        rules.Add(dafny_rule);
      }
      foreach (var rule in context.rule()) {
        var dafny_rule = (_module.Rule) VisitRule(rule);
        rules.Add(dafny_rule);
      }

      return Sequence<_module.Rule>.Create(rules.Count, i => rules[(int) i]);
    }

    public override object VisitFact(datalogParser.FactContext context) {
      var head = (_IProp) VisitClause(context.clause());
      var body = Dafny.Sequence<_IProp>.Empty;
      return new _module.Rule(head, body, RuleID(context));
    }

    public override object VisitRule(datalogParser.RuleContext context) {
      var head = (_IProp) VisitClause(context.clause());
      var body = (Dafny.ISequence<_IProp>) VisitClause_list(context.clause_list());
      return new _module.Rule(head, body, RuleID(context));
    }

    private static int RuleID(ParserRuleContext context) {
      return context.Start.Line;
    }

    public override object VisitClause(datalogParser.ClauseContext context) {
      if (context.name.Text == "=" || context.name.Text == "=<") {
        var left = (_module.Term)VisitTerm(context.left);
        var right = (_module.Term)VisitTerm(context.right);
        var terms = new List<_module.Term> { left, right };
        var terms2 = (Dafny.ISequence<_ITerm>) Sequence<_module.Term>.Create(terms.Count, i => terms[(int) i]);
        switch(context.name.Text) {
          case "\\=":
            return new _module.Prop_BuiltinOp(new _module.Builtin_NatNeq(), terms2);
          case "=<":
            return new _module.Prop_BuiltinOp(new _module.Builtin_NatLeq(), terms2);
          case ">=":
            return new _module.Prop_BuiltinOp(new _module.Builtin_NatGeq(), terms2);
          default:
            return new _module.Prop_Eq(left, right);
        }
      } else {
        var name = Sequence<char>.FromString(context.name.Text);
        if (context.term_list() == null ) {
          var terms = new List<_module.Term>();
          var terms2 = Sequence<_module.Term>.Create(terms.Count, i => terms[(int) i]);
          return new _module.Prop_App(name, (Dafny.ISequence<_ITerm>) terms2);
        } else {
          var terms = (Dafny.ISequence<_ITerm>) VisitTerm_list(context.term_list());
          return new _module.Prop_App(name, terms);
        }
      }
    }

    public override object VisitAtom(datalogParser.AtomContext context) {
      return new Term_Const(new Const_Atom(Sequence<char>.FromString(context.val.Text)));
    }

    public override object VisitNatural(datalogParser.NaturalContext context) {
      return new Term_Const(new Const_Nat(BigInteger.Parse(context.numeral.Text)));
    }

    public override object VisitString(datalogParser.StringContext context) {
      return new Term_Const(new Const_Str(Sequence<char>.FromString(context.s.Text)));
    }

    public override object VisitVariable(datalogParser.VariableContext context) {
      return new Term_Var(Sequence<char>.FromString(context.name.Text));
    }

    public override object VisitClause_list(datalogParser.Clause_listContext context) {
      var props = new List<_module.Prop>();
      foreach (var clause in context.clause()) {
        var dafny_prop = (_module.Prop) VisitClause(clause);
        props.Add(dafny_prop);
      }
      return Sequence<_module.Prop>.Create(props.Count, i => props[(int) i]);
    }

    public override object VisitTerm_list(datalogParser.Term_listContext context) {
      var terms = new List<_module.Term>();
      foreach (var term in context.term()) {
        var dafny_term = (_module.Term)VisitTerm(term);
        terms.Add(dafny_term);
      }
      return Sequence<_module.Term>.Create(terms.Count, i => terms[(int) i]);
    }
  }

  public partial class __default
  {

  }
}
