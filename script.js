class Production {
  constructor(prod_str = null, sep = "|", epsilon = "ε") {
    if (prod_str == null) {
      this.left = null;
      this.right = [];
      return;
    }
    var vals = prod_str.trim().replaceAll(" ", "").split("->");
    this.left = vals[0];
    var right = [];
    for (var alt of vals[1].split(sep)) {
      if (alt == "") alt = epsilon;
      else if (alt != epsilon) alt = alt.replaceAll(epsilon, "");
      if (!right.includes(alt)) right.push(alt);
    }
    this.right = right;
  }
  toString() {
    return this.left + "->" + this.right.join("|");
  }
  nonTerminals() {
    var nt = new Set();
    nt.add(this.left);
    for (var alt of this.right) {
      for (var sym of alt) {
        if (sym.match(/[A-Z]/)) nt.add(sym);
      }
    }
    return nt;
  }
}

class NonRecursivePredictiveParser {
  constructor(grammar, epsilon = "ε") {
    this.epsilon = epsilon;
    var productions = {};
    var newSymbols = new Set("ABCDEFGHIJKLMNOPQRSTUVWXYZ");
    this.startSymbol = grammar[0].left;
    for (var production of grammar) {
      var pNT = production.nonTerminals();
      newSymbols = new Set([...newSymbols].filter((x) => !pNT.has(x)));
      var l = production.left;
      if (l in productions) {
        var updatedRight = productions[l].right;
        for (var alt of production.right) {
          updatedRight.push(alt);
        }
        updatedRight.sort();
        productions[l].right = updatedRight;
      } else productions[l] = production;
    }

    // Remove Left Recursion if exists
    var lrps = [];
    for (var l in productions) {
      var production = productions[l];
      var newSymbol = [...newSymbols][0];
      var result = this.eliminateLeftRecursion(production, newSymbol, epsilon);
      if (result == false) {
        lrps.push(production.toString());
        continue;
      }
      newSymbols.delete(newSymbol);
      for (var p of result) {
        p.right.sort();
        productions[p.left] = p;
        lrps.push(p.toString());
      }
    }
    this.lrps = lrps;

    // Remove Ambiguity if exists
    for (var l in productions) {
      var production = productions[l];
      result = this.eliminateAmbiguity(production, newSymbols, epsilon);
      if (result.length == 1) continue;
      for (var p in result) {
        p.right.sort();
        productions[p.left] = p;
        var pNT = p.nonTerminals();
        newSymbols = new Set([...newSymbols].filter((x) => !pNT.has(x)));
      }
    }
    this.productions = productions;

    // Find First
    var first = {};
    for (var l in productions) {
      first[l] = [...this.findFirst(l)];
    }
    this.first = first;

    var follow = {};
    for (var l in productions) {
      follow[l] = [...this.findFollow(l)];
    }
    this.follow = follow;

    var terminals = [];
    for (var l in productions) {
      for (var alt of productions[l].right) {
        for (var sym of alt) {
          if (!sym.match(/[A-Z]/) && !terminals.includes(sym))
            terminals.push(sym);
        }
      }
    }
    this.terminals = terminals;

    var parseMap = {};
    var hasConflicts = false;
    for (var nonTerminal in productions) {
      var row = {};
      for (var sym of first[nonTerminal]) {
        var result = [];
        for (var alt of productions[nonTerminal].right) {
          if (this.isFirst(sym, nonTerminal, alt, productions)) {
            var prod = new Production(`${nonTerminal}->${alt}`);
            if (sym == epsilon) {
              for (var sym of follow[nonTerminal]) {
                if (!(sym in row)) row[sym] = [prod];
                else {
                  if (this.hasProduction(prod, row[sym])) continue;
                  hasConflicts = true;
                  row[sym].push(prod);
                }
              }
            } else {
              if (!(sym in row)) row[sym] = [prod];
              else {
                if (this.hasProduction(prod, row[sym])) continue;
                hasConflicts = true;
                row[sym].push(prod);
              }
            }
          }
        }
      }
      parseMap[nonTerminal] = row;
    }
    this.parseMap = parseMap;
    this.hasConflicts = hasConflicts;
  }

  hasProduction(prod, list) {
    for (var p in list) {
      if (p.toString() == prod.toString()) return true;
    }
    return false;
  }

  firstFollowTableRows() {
    var s = "";
    for (var k in this.productions) {
      s += `<tr><th>${k}</th><td>${this.first[k].join(
        "<span class='seps'>,&nbsp;</span>"
      )}</td><td>${this.follow[k].join(
        "<span class='seps'>,&nbsp;</span>"
      )}</td></tr>`;
    }
    return s;
  }

  parseTable() {
    var s =
      '<table><thead><tr><th colspan="100%" class="brown">PARSE TABLE</th></tr><tr><th></th>';
    for (var terminal of this.terminals.concat(["$"])) {
      if (terminal == this.epsilon) continue;
      s += `<th>${terminal}</th>`;
    }
    s += "</tr></thead>";
    for (var k in this.productions) {
      s += `<tr><th>${k}</th>`;
      var ps = this.parseMap[k];
      for (var terminal of this.terminals.concat(["$"])) {
        if (terminal == this.epsilon) continue;
        if (!(terminal in ps)) {
          s += '<td class="red"></td>';
          continue;
        }
        var po = [];
        for (var p of ps[terminal]) {
          po.push(p.toString());
        }
        if (po.length > 1) s += `<td class="conflict">${po.join("<br>")}</td>`;
        else s += `<td>${po[0]}</td>`;
      }
      s += "</tr>";
    }
    return s + "</table>";
  }

  leftRecursionExists(production) {
    for (var alt of production.right) {
      if (alt[0] == production.left) return true;
    }
    return false;
  }

  eliminateLeftRecursion(production, newSymbol) {
    var newProduction = new Production();
    newProduction.left = newSymbol;
    var updatedRight = [];
    if (!this.leftRecursionExists(production)) return false;
    for (var alt of production.right) {
      if (production.left == alt[0])
        newProduction.right.push(alt.substring(1) + newSymbol);
      else if (alt == this.epsilon) updatedRight.push(newSymbol);
      else updatedRight.push(alt + newSymbol);
    }
    newProduction.right.push(this.epsilon);
    production.right = updatedRight;
    return [production, newProduction];
  }

  findCommonFactors(production) {
    var factors = new Set(),
      compvared = new Set();
    for (var i = 0; i < production.right.length; ++i) {
      var cAlt = production.right[i];
      var neglected = new Set();
      neglected.add(i);
      var commonUpto = -1;
      for (var j = 0; j < cAlt.length; ++j) {
        var sym = cAlt[j];
        var isCommon = 0;
        for (var k = 0; k < production.right.length; ++k) {
          var alt = production.right[k];
          if (neglected.has(k) || j >= alt.length) continue;
          if (sym == alt[j]) {
            isCommon += 1;
            continue;
          }
          if (j == 0) neglected.add(k);
          else break;
        }
        if (
          isCommon > 0 &&
          isCommon == production.right.length - neglected.size
        )
          commonUpto = j;
        else break;
      }
      if (commonUpto > -1) factors.add(cAlt.substring(0, commonUpto + 1));
      for (var j = 0; j < production.right.length; ++j) {
        if (!neglected.has(j)) compvared.add(i);
      }
    }
    return factors;
  }

  leftFactorize(production, commonFactors, newSymbols) {
    var newProductions = [];
    newSymbols = [...newSymbols];
    for (var i = 0; i < commonFactors.length; ++i) {
      var commonFactor = commonFactors[i];
      var newSymbol = newSymbols[i];
      var newProduction = new Production();
      newProduction.left = newSymbol;
      var updatedRight = [];
      for (var alt of production.right) {
        if (alt.startsWith(commonFactor)) {
          var rem = alt.substring(commonFactor.length);
          if (rem == "") rem = this.epsilon;
          newProduction.right.push(rem);
        } else updatedRight.push(alt);
      }
      production.right = [commonFactor + newSymbol].concat(updatedRight);
      newProductions.push(newProduction);
    }
    return [production, newProductions];
  }

  eliminateAmbiguity(production, newSymbols) {
    var commonFactors = this.findCommonFactors(production);
    var newProductions = [];
    if (commonFactors.length == 0) return [production].concat(newProductions);
    var [production, newPs] = this.leftFactorize(
      production,
      commonFactors,
      newSymbols
    );
    var pNT = production.nonTerminals();
    newSymbols = new Set([...newSymbols].filter((x) => !pNT.has(x)));
    for (var newP of newPs) {
      var updatedPs = this.eliminateAmbiguity(newP, newSymbols);
      for (var updatedP of updatedPs) {
        if (!newProductions.includes(updatedP)) {
          newProductions.push(updatedP);
        }
      }
    }
    return [production].concat(newProductions);
  }

  findFirst(nonTerminal) {
    var syms = new Set();
    for (var alt of this.productions[nonTerminal].right) {
      for (var i = 0; i < alt.length; ++i) {
        var c = alt[i];
        if (c == nonTerminal) continue;
        else if (c.match(/[A-Z]/)) {
          var hasEpsilon = false;
          for (var sym of this.findFirst(c).values()) {
            if (sym == this.epsilon) hasEpsilon = true;
            else syms.add(sym);
          }
          if (hasEpsilon && i == alt.length - 1) syms.add(this.epsilon);
          else if (!hasEpsilon) break;
        } else {
          syms.add(c);
          break;
        }
      }
    }
    return syms;
  }

  findFollow(nonTerminal, track = []) {
    var syms = new Set();
    track.push(nonTerminal);
    if (nonTerminal == this.startSymbol) syms.add("$");
    for (var k in this.productions) {
      var production = this.productions[k];
      for (var alt of production.right) {
        var i = alt.indexOf(nonTerminal);
        if (i++ == -1) continue;
        for (; i < alt.length; ++i) {
          var c = alt[i];
          if (c.match(/[A-Z]/)) {
            var hasEpsilon = false;
            for (var sym of this.first[c]) {
              if (sym == this.epsilon) hasEpsilon = true;
              else syms.add(sym);
            }
            if (!hasEpsilon) break;
          } else {
            syms.add(c);
            break;
          }
        }
        var l = production.left;
        if (i == alt.length && l != nonTerminal) {
          if (!track.includes(l))
            for (var fs of this.findFollow(l, track).values()) {
              syms.add(fs);
            }
        }
      }
    }
    return syms;
  }

  isFirst(symbol, nT, alt) {
    var sym = alt[0];
    if (sym.match(/[A-Z]/)) {
      for (var alt of this.productions[sym].right) {
        if (this.isFirst(symbol, nT, alt)) return true;
      }
    } else if (sym == symbol) return true;
    return false;
  }

  parse(string) {
    string = string.replaceAll(" ", "") + "$";
    var stack = ["$", this.startSymbol];
    var opRows = "";
    var top = stack.at(-1);
    while (!(top == "$" && string[0] == "$")) {
      opRows += `<tr><td>${stack.join(
        " "
      )}</td><td class="inp-la">${string}</td>`;
      var rs = "";
      var char = string[0];
      var isAccepted = true;
      if (top.match(/[A-Z]/)) {
        if (!(char in this.parseMap[top])) {
          isAccepted = false;
          break;
        }
        var p = this.parseMap[top][char][0];
        rs = p.toString();
        var rule = p.right[0];
        stack.pop();
        for (var i = rule.length - 1; i >= 0; --i) {
          var sym = rule[i];
          if (sym != this.epsilon) stack.push(sym);
        }
      } else if (string[0] == top) {
        stack.pop();
        string = string.substring(1);
      } else {
        isAccepted = false;
        break;
      }
      top = stack.at(-1);
      opRows += `<td class="inp-c">${rs}</td></tr>`;
    }
    if (isAccepted)
      opRows += `<tr><td>${stack.join(
        " "
      )}</td><td class="inp-la">${string}</td><td class="inp-c accepted">Accepted</td></tr>`;
    else opRows += '<td class="inp-c unaccepted">Error</td></tr>';
    return opRows;
  }
}

var parser;

function construct() {
  try {
    var grammar = document.getElementById("grammar").value;
    grammar = grammar.trim().replaceAll(" ", "").split("\n");
    var productions = [];
    for (var prodStr of grammar) {
      prodStr = prodStr.trim();
      if (prodStr == "") continue;
      var production = new Production(prodStr);
      production.right.sort();
      productions.push(production);
    }
    document.getElementById("data").innerHTML = productions.join("<br>");
    parser = new NonRecursivePredictiveParser(productions);
    var ps = [];
    for (var k in parser.productions) ps.push(parser.productions[k].toString());
    document.getElementById("lrp").innerHTML = parser.lrps.join("<br>");
    document.getElementById("lfp").innerHTML = ps.join("<br>");
    document.getElementById("ffb").innerHTML = parser.firstFollowTableRows();
    document.getElementById("pt").innerHTML = parser.parseTable();
    if (parser.hasConflicts) {
      document.getElementById("ll1-err").classList.remove("hidden");
      document.getElementById("prse").classList.add("hidden");
    } else {
      document.getElementById("ll1-err").classList.add("hidden");
      document.getElementById("prse").classList.remove("hidden");
    }
    document.getElementById("construction-err").classList.add("hidden");
    document.getElementById("construction").classList.remove("hidden");
  } catch (error) {
    console.log(error);
    document.getElementById("construction").classList.add("hidden");
    document.getElementById("construction-err").classList.remove("hidden");
  }
}

function parseString() {
  var element = document.getElementById("string");
  var string = element.value;
  var result = parser.parse(string);
  var pr = `<table>
    <thead>
      <tr><th class="brown" colspan="100%">INPUT PARSING</th></tr>
      <tr>
        <th>Stack</th>
        <th>Input</th>
        <th>Action</th>
      </tr>
    </thead>
    <tbody id="ipt">
      ${result}
    </tbody>
  </table>`;
  document.getElementById("pr").innerHTML = pr;
}

var examples = [
  "E->E+T|T\nT->T*F|F\nF->(E)|d",
  "S->L=R|R\nR->L\nL->*R|d",
  "S->CC\nC->cC|d",
];

function setExample(n) {
  document.getElementById("grammar").value = examples[n - 1];
}

function insertEpsilon() {
  document.getElementById("grammar").value += "ε";
}
