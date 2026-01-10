package hscript;

import hscript.Expr;
import StringTools;

class Optimizer {
	public var enabled:Bool = true;
	public var optimizeLevel:Int = 2;
	
	public var enableConstantFolding:Bool = true;
	public var enableExpressionSimplification:Bool = true;
	public var enableDeadCodeElimination:Bool = true;
	public var enableBranchOptimization:Bool = true;
	
	public var debug:Bool = false;
	public var debugPrinter:Printer;

	public function new() {
		debugPrinter = new Printer();
	}

	public function optimize(expr:Expr):Expr {
		if (!enabled) return expr;
		
		if (debug) {
			trace("=== HScript Optimizer Debug ===");
			trace("Optimization Level: " + optimizeLevel);
			trace("Constant Folding: " + enableConstantFolding);
			trace("Expression Simplification: " + enableExpressionSimplification);
			trace("Dead Code Elimination: " + enableDeadCodeElimination);
			trace("Branch Optimization: " + enableBranchOptimization);
			trace("\n--- Original Code ---");
			trace(debugPrinter.exprToString(expr));
		}
		
		var result = expr;
		var startTime = Sys.time();
		var passTimes:Array<Float> = [];
		
		for (i in 0...optimizeLevel) {
			var passStart = Sys.time();
			var beforeStr = debugPrinter.exprToString(result);
			result = optimizeOnce(result);
			var afterStr = debugPrinter.exprToString(result);
			var passTime = (Sys.time() - passStart) * 1000;
			passTimes.push(passTime);
			
			if (debug) {
				var optimizedCount = beforeStr.length - afterStr.length;
				trace("\n--- After Pass " + (i + 1) + " (" + Math.round(passTime * 100) / 100 + " ms, reduced " + optimizedCount + " chars) ---");
				trace(afterStr);
			}
			
			if (beforeStr == afterStr) {
				if (debug) {
					trace("\n--- No further optimizations possible after pass " + (i + 1) + " ---");
				}
				break;
			}
		}
		
		var totalTime = (Sys.time() - startTime) * 1000;
		
		if (debug) {
			trace("\n--- Optimization Complete ---");
			trace("Total passes: " + passTimes.length);
			trace("Total time: " + Math.round(totalTime * 100) / 100 + " ms");
			if (passTimes.length > 1) {
				trace("Average per pass: " + Math.round((totalTime / passTimes.length) * 100) / 100 + " ms");
			}
			trace("=== End Debug ===\n");
		}
		
		return result;
	}

	private function optimizeOnce(expr:Expr):Expr {
		return switch (Tools.expr(expr)) {
			case EConst(_): return expr;
			case EIdent(_): return expr;
			case EPackage(_): return expr;
			case EImport(_): return expr;
			case EClass(name, fields, extend, interfaces, isFinal):
				var optimizedFields = [for (f in fields) optimizeOnce(f)];
				return Tools.mk(EClass(name, optimizedFields, extend, interfaces, isFinal), expr);
			case EVar(n, t, e, isPublic, isStatic, isPrivate, isFinal, isInline, get, set, isVar):
				var optimizedExpr = e != null ? optimizeOnce(e) : null;
				return Tools.mk(EVar(n, t, optimizedExpr, isPublic, isStatic, isPrivate, isFinal, isInline, get, set, isVar), expr);
			case EParent(e):
				var optimized = optimizeOnce(e);
				return Tools.mk(EParent(optimized), expr);
			case EBlock(exprs):
				var optimizedExprs = [for (e in exprs) optimizeOnce(e)];
				var cleanedExprs = enableDeadCodeElimination ? removeDeadCode(optimizedExprs) : optimizedExprs;
				if (cleanedExprs.length == 1) {
					return cleanedExprs[0];
				} else {
					return Tools.mk(EBlock(cleanedExprs), expr);
				}
			case EField(e, f, s):
				var optimized = optimizeOnce(e);
				return Tools.mk(EField(optimized, f, s), expr);
			case EBinop(op, e1, e2):
				var optimized1 = optimizeOnce(e1);
				var optimized2 = optimizeOnce(e2);
				var folded = enableConstantFolding ? tryFoldConstant(op, optimized1, optimized2) : null;
				if (folded != null) {
					return folded;
				} else {
					var simplified = enableExpressionSimplification ? trySimplifyBinop(op, optimized1, optimized2) : null;
					if (simplified != null) {
						return simplified;
					} else {
						return Tools.mk(EBinop(op, optimized1, optimized2), expr);
					}
				}
			case EUnop(op, prefix, e):
				var optimized = optimizeOnce(e);
				var folded = enableConstantFolding ? tryFoldUnop(op, prefix, optimized) : null;
				if (folded != null) {
					return folded;
				} else {
					var simplified = enableExpressionSimplification ? trySimplifyUnop(op, prefix, optimized) : null;
					if (simplified != null) {
						return simplified;
					} else {
						return Tools.mk(EUnop(op, prefix, optimized), expr);
					}
				}
			case ECall(e, params):
				var optimizedExpr = optimizeOnce(e);
				var optimizedParams = [for (p in params) optimizeOnce(p)];
				return Tools.mk(ECall(optimizedExpr, optimizedParams), expr);
			case EIf(cond, e1, e2):
				var optimizedCond = optimizeOnce(cond);
				var optimizedE1 = optimizeOnce(e1);
				var optimizedE2 = e2 != null ? optimizeOnce(e2) : null;
				
				if (enableBranchOptimization) {
					var optimized = tryOptimizeIf(optimizedCond, optimizedE1, optimizedE2);
					if (optimized != null) {
						return optimized;
					}
				}
				return Tools.mk(EIf(optimizedCond, optimizedE1, optimizedE2), expr);
			case EWhile(cond, e):
				var optimizedCond = optimizeOnce(cond);
				var optimizedBody = optimizeOnce(e);
				return Tools.mk(EWhile(optimizedCond, optimizedBody), expr);
			case EDoWhile(cond, e):
				var optimizedCond = optimizeOnce(cond);
				var optimizedBody = optimizeOnce(e);
				return Tools.mk(EDoWhile(optimizedCond, optimizedBody), expr);
			case EFor(v, it, e, ithv):
				var optimizedIt = optimizeOnce(it);
				var optimizedBody = optimizeOnce(e);
				return Tools.mk(EFor(v, optimizedIt, optimizedBody, ithv), expr);
			case EBreak: return expr;
			case EContinue: return expr;
			case EFunction(args, e, name, ret, isPublic, isStatic, isOverride, isPrivate, isFinal, isInline):
				var optimizedBody = optimizeOnce(e);
				return Tools.mk(EFunction(args, optimizedBody, name, ret, isPublic, isStatic, isOverride, isPrivate, isFinal, isInline), expr);
			case EReturn(e):
				var optimized = e != null ? optimizeOnce(e) : null;
				return Tools.mk(EReturn(optimized), expr);
			case EArray(e, index):
				var optimizedExpr = optimizeOnce(e);
				var optimizedIndex = optimizeOnce(index);
				return Tools.mk(EArray(optimizedExpr, optimizedIndex), expr);
			case EArrayDecl(exprs, wantedType):
				var optimizedExprs = [for (e in exprs) optimizeOnce(e)];
				return Tools.mk(EArrayDecl(optimizedExprs, wantedType), expr);
			case ENew(cl, params, paramType):
				var optimizedParams = [for (p in params) optimizeOnce(p)];
				return Tools.mk(ENew(cl, optimizedParams, paramType), expr);
			case EThrow(e):
				var optimized = optimizeOnce(e);
				return Tools.mk(EThrow(optimized), expr);
			case ETry(e, v, t, ecatch):
				var optimizedTry = optimizeOnce(e);
				var optimizedCatch = optimizeOnce(ecatch);
				return Tools.mk(ETry(optimizedTry, v, t, optimizedCatch), expr);
			case EObject(fl):
				var optimizedFields = [for (f in fl) {name: f.name, e: optimizeOnce(f.e)}];
				var objectFields:Array<ObjectField> = [];
				for (f in optimizedFields) {
					objectFields.push({name: f.name, e: f.e});
				}
				return Tools.mk(EObject(objectFields), expr);
			case ETernary(cond, e1, e2):
				var optimizedCond = optimizeOnce(cond);
				var optimizedE1 = optimizeOnce(e1);
				var optimizedE2 = optimizeOnce(e2);
				
				if (enableBranchOptimization) {
					var optimized = tryOptimizeTernary(optimizedCond, optimizedE1, optimizedE2);
					if (optimized != null) {
						return optimized;
					}
				}
				return Tools.mk(ETernary(optimizedCond, optimizedE1, optimizedE2), expr);
			case ESwitch(e, cases, defaultExpr):
				var optimizedExpr = optimizeOnce(e);
				var optimizedCases = [for (c in cases) {
					values: [for (v in c.values) optimizeOnce(v)],
					expr: optimizeOnce(c.expr)
				}];
				var switchCases:Array<SwitchCase> = [];
				for (c in optimizedCases) {
					switchCases.push({values: c.values, expr: c.expr});
				}
				var optimizedDefault = defaultExpr != null ? optimizeOnce(defaultExpr) : null;
				return Tools.mk(ESwitch(optimizedExpr, switchCases, optimizedDefault), expr);
			case EMeta(name, args, e):
				var optimizedArgs = args != null ? [for (a in args) optimizeOnce(a)] : null;
				var optimizedExpr = optimizeOnce(e);
				return Tools.mk(EMeta(name, optimizedArgs, optimizedExpr), expr);
			case ECheckType(e, t):
				var optimized = optimizeOnce(e);
				return Tools.mk(ECheckType(optimized, t), expr);
			case EEnum(en, isAbstract):
				return Tools.mk(EEnum(en, isAbstract), expr);
			case ECast(e, t):
				var optimized = optimizeOnce(e);
				return Tools.mk(ECast(optimized, t), expr);
			case ERegex(e, f):
				return Tools.mk(ERegex(e, f), expr);
		}
	}

	private function tryFoldConstant(op:String, e1:Expr, e2:Expr):Null<Expr> {
		var c1 = getConstValue(e1);
		var c2 = getConstValue(e2);
		
		if (c1 == null || c2 == null) return null;
		
		var result:Dynamic = null;
		
		try {
			switch (op) {
				case "+": result = c1 + c2;
				case "-": result = c1 - c2;
				case "*": result = c1 * c2;
				case "/": 
					if (c2 == 0) return null;
					result = c1 / c2;
				case "%": 
					if (c2 == 0) return null;
					result = c1 % c2;
				case "&": result = c1 & c2;
				case "|": result = c1 | c2;
				case "^": result = c1 ^ c2;
				case "<<": result = c1 << c2;
				case ">>": result = c1 >> c2;
				case ">>>": result = c1 >>> c2;
				case "==": result = c1 == c2;
				case "!=": result = c1 != c2;
				case ">": result = c1 > c2;
				case "<": result = c1 < c2;
				case ">=": result = c1 >= c2;
				case "<=": result = c1 <= c2;
				case "&&": result = (c1 == true) && (c2 == true);
				case "||": result = (c1 == true) || (c2 == true);
				default: return null;
			}
		} catch (e:Dynamic) {
			return null;
		}
		
		return makeConst(result, e1);
	}

	private function tryFoldUnop(op:String, prefix:Bool, e:Expr):Null<Expr> {
		var c = getConstValue(e);
		if (c == null) return null;
		
		var result:Dynamic = null;
		
		try {
			switch (op) {
				case "!": result = !(c == true);
				case "-": result = -c;
				case "~": result = ~c;
				default: return null;
			}
		} catch (e:Dynamic) {
			return null;
		}
		
		return makeConst(result, e);
	}

	private function trySimplifyBinop(op:String, e1:Expr, e2:Expr):Null<Expr> {
		var c1 = getConstValue(e1);
		var c2 = getConstValue(e2);
		
		switch (op) {
			case "+":
				if (c1 != null && c1 == 0 && !isStringExpr(e1)) return e2;
				if (c2 != null && c2 == 0 && !isStringExpr(e2)) return e1;
				
				if (c1 != null && c2 != null) {
					return makeConst(c1 + c2, e1);
				}
				
				if (c1 != null) {
					switch (Tools.expr(e2)) {
						case EBinop("+", e2_1, e2_2):
							var c2_1 = getConstValue(e2_1);
							var c2_2 = getConstValue(e2_2);
							if (c2_1 != null && c2_2 != null) {
								var combinedConst = c1 + c2_1 + c2_2;
								return Tools.mk(EBinop("+", e2_1, makeConst(c2_2 + c1, e2_2)), e2);
							}
							if (c2_1 != null) {
								var combinedConst = c1 + c2_1;
								return Tools.mk(EBinop("+", makeConst(combinedConst, e2_1), e2_2), e2);
							}
						case EBinop("-", e2_1, e2_2):
							var c2_1 = getConstValue(e2_1);
							var c2_2 = getConstValue(e2_2);
							if (c2_1 != null && c2_2 != null) {
								var combinedConst = c1 - c2_1 + c2_2;
								return Tools.mk(EBinop("+", e2_1, makeConst(c2_2 + c1, e2_2)), e2);
							}
							if (c2_1 != null) {
								var combinedConst = c1 - c2_1;
								return Tools.mk(EBinop("+", makeConst(combinedConst, e2_1), e2_2), e2);
							}
						default:
					}
				}
				
				if (c2 != null) {
					switch (Tools.expr(e1)) {
						case EBinop("+", e1_1, e1_2):
							var c1_1 = getConstValue(e1_1);
							var c1_2 = getConstValue(e1_2);
							if (c1_1 != null && c1_2 != null) {
								var combinedConst = c1_1 + c1_2 + c2;
								return Tools.mk(EBinop("+", e1_1, makeConst(c1_2 + c2, e1_2)), e1);
							}
							if (c1_2 != null) {
								return Tools.mk(EBinop("+", e1, makeConst(c2, e2)), e1);
							}
						case EBinop("-", e1_1, e1_2):
							var c1_1 = getConstValue(e1_1);
							var c1_2 = getConstValue(e1_2);
							if (c1_1 != null && c1_2 != null) {
								var combinedConst = c1_1 - c1_2 + c2;
								return Tools.mk(EBinop("-", e1_1, makeConst(c1_2 - c2, e1_2)), e1);
							}
							if (c1_2 != null) {
								if (op == "+") {
									return Tools.mk(EBinop("-", e1_1, makeConst(c1_2 - c2, e1_2)), e1);
								} else {
									return Tools.mk(EBinop("-", e1_1, makeConst(c1_2 + c2, e1_2)), e1);
								}
							}
						case EBinop("*", e1_1, e1_2):
							var c1_1 = getConstValue(e1_1);
							var c1_2 = getConstValue(e1_2);
							if (c1_1 != null && c1_2 != null) {
								var combinedConst = c1_1 * c1_2;
								return Tools.mk(EBinop("*", e1_1, makeConst(combinedConst, e1_2)), e1);
							}
						case EBinop("/", e1_1, e1_2):
							var c1_1 = getConstValue(e1_1);
							var c1_2 = getConstValue(e1_2);
							if (c1_1 != null && c1_2 != null) {
								var combinedConst = c1_1 / c1_2;
								return Tools.mk(EBinop("/", e1_1, makeConst(combinedConst, e1_2)), e1);
							}
						default:
					}
				}
			case "-":
				if (c2 != null && c2 == 0) return e1;
				
				if (c1 != null && c2 != null) {
					return makeConst(c1 - c2, e1);
				}
				
				if (c1 != null) {
					switch (Tools.expr(e2)) {
						case EBinop("-", e2_1, e2_2):
							var c2_1 = getConstValue(e2_1);
							var c2_2 = getConstValue(e2_2);
							if (c2_1 != null && c2_2 != null) {
								var combinedConst = c1 - c2_1 - c2_2;
								return Tools.mk(EBinop("-", e2_1, makeConst(c2_2 - c1, e2_2)), e2);
							}
							if (c2_1 != null) {
								var combinedConst = c1 - c2_1;
								return Tools.mk(EBinop("-", makeConst(combinedConst, e2_1), e2_2), e2);
							}
						case EBinop("/", e2_1, e2_2):
							var c2_1 = getConstValue(e2_1);
							var c2_2 = getConstValue(e2_2);
							if (c2_1 != null && c2_2 != null) {
								var combinedConst = c1 - c2_1 / c2_2;
								return Tools.mk(EBinop("-", e2_1, makeConst(c2_2, e2_2)), e2);
							}
							if (c2_1 != null) {
								var combinedConst = c1 - c2_1;
								return Tools.mk(EBinop("-", makeConst(combinedConst, e2_1), e2_2), e2);
							}
						default:
					}
				}
				
				if (c2 != null) {
					switch (Tools.expr(e1)) {
						case EBinop("+", e1_1, e1_2):
							var c1_2 = getConstValue(e1_2);
							if (c1_2 != null) {
								var combinedConst = c1_2 - c2;
								return Tools.mk(EBinop("+", e1_1, makeConst(combinedConst, e1_2)), e1);
							}
						case EBinop("-", e1_1, e1_2):
							var c1_2 = getConstValue(e1_2);
							if (c1_2 != null) {
								var combinedConst = c1_2 + c2;
								return Tools.mk(EBinop("-", e1_1, makeConst(combinedConst, e1_2)), e1);
							}
						default:
					}
				}
			case "*":
				if (c1 != null && c1 == 1) return e2;
				if (c2 != null && c2 == 1) return e1;
				if ((c1 != null && c1 == 0) || (c2 != null && c2 == 0)) return makeConst(0, e1);
				
				if (c1 != null && c2 != null) {
					return makeConst(c1 * c2, e1);
				}
				
				if (c1 != null) {
					switch (Tools.expr(e2)) {
						case EBinop("*", e2_1, e2_2):
							var c2_1 = getConstValue(e2_1);
							var c2_2 = getConstValue(e2_2);
							if (c2_1 != null && c2_2 != null) {
								var combinedConst = c1 * c2_1 * c2_2;
								return Tools.mk(EBinop("*", e2_1, makeConst(c2_2 * c1, e2_2)), e2);
							}
							if (c2_1 != null) {
								var combinedConst = c1 * c2_1;
								return Tools.mk(EBinop("*", makeConst(combinedConst, e2_1), e2_2), e2);
							}
						default:
					}
				}
				
				if (c2 != null) {
					switch (Tools.expr(e1)) {
						case EBinop("*", e1_1, e1_2):
							var c1_1 = getConstValue(e1_1);
							var c1_2 = getConstValue(e1_2);
							if (c1_1 != null && c1_2 != null) {
								var combinedConst = c1_1 * c1_2 * c2;
								return Tools.mk(EBinop("*", e1_1, makeConst(c1_2 * c2, e1_2)), e1);
							}
							if (c1_2 != null) {
								var combinedConst = c1_2 * c2;
								return Tools.mk(EBinop("*", e1_1, makeConst(combinedConst, e1_2)), e1);
							}
						default:
					}
				}
			case "/":
				if (c2 != null && c2 == 1) return e1;
				if (c2 != null && c2 != 0) {
					var multiplier = 1.0 / c2;
					return Tools.mk(EBinop("*", e1, makeConst(multiplier, e2)), e2);
				}
				
				if (c1 != null) {
					switch (Tools.expr(e2)) {
						case EBinop("*", e2_1, e2_2):
							var c2_1 = getConstValue(e2_1);
							var c2_2 = getConstValue(e2_2);
							if (c2_1 != null && c2_2 != null) {
								var combinedConst = c2_1 * c2_2;
								var multiplier = 1.0 / combinedConst;
								return Tools.mk(EBinop("*", e1, makeConst(multiplier, e2_1)), e2_2);
							}
							if (c2_1 != null) {
							var multiplier = 1.0 / c2_1;
							return Tools.mk(EBinop("*", e1, makeConst(multiplier, e2_1)), e2_2);
						}
						case EBinop("/", e2_1, e2_2):
							var c2_1 = getConstValue(e2_1);
							var c2_2 = getConstValue(e2_2);
							if (c2_1 != null && c2_2 != null) {
								var combinedConst = c2_1 / c2_2;
								var multiplier = 1.0 / combinedConst;
								return Tools.mk(EBinop("*", e1, makeConst(multiplier, e2_1)), e2_2);
							}
						default:
					}
				}
				
				if (c2 != null) {
					switch (Tools.expr(e1)) {
						case EBinop("*", e1_1, e1_2):
							var c1_1 = getConstValue(e1_1);
							var c1_2 = getConstValue(e1_2);
							if (c1_1 != null && c1_2 != null) {
								var combinedConst = c1_1 * c1_2;
								var multiplier = 1.0 / c2;
								return Tools.mk(EBinop("*", e1_1, makeConst(c1_2 * multiplier, e1_2)), e2);
							}
							if (c1_2 != null) {
								var multiplier = 1.0 / c2;
								return Tools.mk(EBinop("/", e1_1, makeConst(c1_2 / c2, e1_2)), e2);
							}
						case EBinop("/", e1_1, e1_2):
						var c1_1 = getConstValue(e1_1);
						var c1_2 = getConstValue(e1_2);
						if (c1_1 != null && c1_2 != null) {
							var combinedConst = c1_1 / c1_2;
							var multiplier = 1.0 / combinedConst;
							return Tools.mk(EBinop("*", e1_1, makeConst(multiplier, e1_2)), e2);
						}
						if (c1_2 != null) {
							var multiplier = 1.0 / c1_2;
							return Tools.mk(EBinop("/", e1_1, makeConst(multiplier, e1_2)), e2);
						}
						if (c1_1 != null) {
							var multiplier = 1.0 / c1_1;
							return Tools.mk(EBinop("/", e1_1, makeConst(multiplier, e1_2)), e2);
						}
					default:
					}
				}
			case "&&":
				if (c1 != null && c1 == false) return makeConst(false, e1);
				if (c2 != null && c2 == false) return makeConst(false, e2);
				if (c1 != null && c1 == true) return e2;
				if (c2 != null && c2 == true) return e1;
			case "||":
				if (c1 != null && c1 == true) return makeConst(true, e1);
				if (c2 != null && c2 == true) return makeConst(true, e2);
				if (c1 != null && c1 == false) return e2;
				if (c2 != null && c2 == false) return e1;
			case "%":
				if (c2 != null && c2 == 1) return makeConst(0, e1);
				if (c1 != null && c2 != null) {
					return makeConst(c1 % c2, e1);
				}
				if (c2 != null && isPowerOfTwo(c2) && c1 != null && c1 >= 0) {
					var mask = Std.int(c2) - 1;
					return Tools.mk(EBinop("&", e1, makeConst(mask, e2)), e1);
				}
		}
		
		return null;
	}

	private function trySimplifyUnop(op:String, prefix:Bool, e:Expr):Null<Expr> {
		switch (Tools.expr(e)) {
			case EUnop(op2, prefix2, e2):
				if (op == op2 && prefix != prefix2) {
					return e2;
				}
			default:
		}
		
		return null;
	}

	private function tryOptimizeIf(cond:Expr, e1:Expr, e2:Expr):Null<Expr> {
		var c = getConstValue(cond);
		
		if (c != null && isPureConstant(cond)) {
			if (c == true) {
				return e1;
			} else {
				return e2 != null ? e2 : makeConst(null, cond);
			}
		}
		
		if (exprEquals(e1, e2)) {
			return e1;
		}
		
		return null;
	}

	private function tryOptimizeTernary(cond:Expr, e1:Expr, e2:Expr):Null<Expr> {
		var c = getConstValue(cond);
		
		if (c != null && isPureConstant(cond)) {
			if (c == true) {
				return e1;
			} else {
				return e2;
			}
		}
		
		if (exprEquals(e1, e2)) {
			return e1;
		}
		
		return null;
	}

	private function removeDeadCode(exprs:Array<Expr>):Array<Expr> {
		var result:Array<Expr> = [];
		var foundTerminator = false;
		
		for (e in exprs) {
			if (foundTerminator) {
				if (hasSideEffects(e)) {
					result.push(e);
				}
			} else {
				result.push(e);
				
				if (isUnconditionalTerminator(e)) {
					foundTerminator = true;
				}
			}
		}
		
		return result;
	}
	
	private function isUnconditionalTerminator(expr:Expr):Bool {
		return switch (Tools.expr(expr)) {
			case EReturn(_): true;
			case EThrow(_): true;
			default: false;
		}
	}

	private function isTerminator(expr:Expr):Bool {
		return switch (Tools.expr(expr)) {
			case EBreak, EContinue, EReturn(_): true;
			default: false;
		}
	}

	private function getConstValue(expr:Expr):Null<Dynamic> {
		return switch (Tools.expr(expr)) {
			case EConst(CInt(v)): v;
			case EConst(CFloat(v)): v;
			case EConst(CString(v)): v;
			default: null;
		}
	}

	private function makeConst(value:Dynamic, original:Expr):Expr {
		if (Std.isOfType(value, Int)) {
			return Tools.mk(EConst(CInt(value)), original);
		} else if (Std.isOfType(value, Float)) {
			return Tools.mk(EConst(CFloat(value)), original);
		} else if (Std.isOfType(value, String)) {
			return Tools.mk(EConst(CString(value)), original);
		} else if (value == null) {
			return Tools.mk(EConst(CInt(0)), original);
		} else {
			return Tools.mk(EConst(CFloat(value)), original);
		}
	}

	private function exprEquals(e1:Expr, e2:Expr):Bool {
		if (e1 == e2) return true;
		if (e1 == null || e2 == null) return false;
		
		return switch ([Tools.expr(e1), Tools.expr(e2)]) {
			case [EConst(c1), EConst(c2)]:
				switch ([c1, c2]) {
					case [CInt(v1), CInt(v2)]: v1 == v2;
					case [CFloat(v1), CFloat(v2)]: v1 == v2;
					case [CString(v1), CString(v2)]: v1 == v2;
					default: false;
				}
			case [EIdent(v1), EIdent(v2)]: v1 == v2;
			default: false;
		}
	}

	private function hasSideEffects(expr:Expr):Bool {
		return switch (Tools.expr(expr)) {
			case ECall(_, _): true;
			case EBinop("=", _, _): true;
			case EBinop(op, _, _) if (StringTools.endsWith(op, "=")): true;
			case EUnop("++", _, _) | EUnop("--", _, _): true;
			case EField(e, _, _): hasSideEffects(e);
			case EArray(e, index): hasSideEffects(e) || hasSideEffects(index);
			case ENew(_, _, _): true;
			case EThrow(_): true;
			case EVar(_, _, e, _, _, _, _, _, _, _, _):
				e != null ? hasSideEffects(e) : false;
			case EObject(fields):
				for (f in fields) {
					if (hasSideEffects(f.e)) return true;
				}
				false;
			case EArrayDecl(exprs):
				for (e in exprs) {
					if (hasSideEffects(e)) return true;
				}
				false;
			case ESwitch(e, cases, defaultExpr):
				if (hasSideEffects(e)) return true;
				for (c in cases) {
					for (v in c.values) {
						if (hasSideEffects(v)) return true;
					}
					if (hasSideEffects(c.expr)) return true;
				}
				if (defaultExpr != null && hasSideEffects(defaultExpr)) return true;
				false;
			case EIf(cond, e1, e2):
				hasSideEffects(cond) || hasSideEffects(e1) || (e2 != null && hasSideEffects(e2));
			case EWhile(cond, e) | EDoWhile(cond, e):
				hasSideEffects(cond) || hasSideEffects(e);
			case EFor(_, it, e, _):
				hasSideEffects(it) || hasSideEffects(e);
			case ETernary(cond, e1, e2):
				hasSideEffects(cond) || hasSideEffects(e1) || hasSideEffects(e2);
			case EFunction(_, _, _, _, _, _, _, _, _, _): false;
			case EConst(_): false;
			case EIdent(_): false;
			case EParent(e): hasSideEffects(e);
			case EBlock(exprs):
				for (e in exprs) {
					if (hasSideEffects(e)) return true;
				}
				false;
			case EReturn(e):
				e != null ? hasSideEffects(e) : false;
			case EBreak, EContinue: false;
			case ECheckType(e, _): hasSideEffects(e);
			case ECast(e, _): hasSideEffects(e);
			case EMeta(_, _, e): hasSideEffects(e);
			case EPackage(_): false;
			case EImport(_): false;
			case EClass(_, _, _, _, _): false;
			case EEnum(_, _): false;
			default: true;
		}
	}

	private function isPureConstant(expr:Expr):Bool {
		return switch (Tools.expr(expr)) {
			case EConst(_): true;
			case EParent(e): isPureConstant(e);
			default: false;
		}
	}

	private function isStringExpr(expr:Expr):Bool {
		return switch (Tools.expr(expr)) {
			case EConst(CString(_)): true;
			case EParent(e): isStringExpr(e);
			case EBinop("+", e1, e2): isStringExpr(e1) || isStringExpr(e2);
			default: false;
		}
	}
	
	private function isPowerOfTwo(n:Float):Bool {
		if (n != Math.floor(n)) return false;
		var i = Std.int(n);
		if (i <= 0) return false;
		return (i & (i - 1)) == 0;
	}
}