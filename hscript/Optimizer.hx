package hscript;

import haxe.ds.StringMap;
import haxe.ds.IntMap;
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
	
	private var optimizationCache:StringMap<Expr>;
	private var exprHashes:IntMap<String>;
	private var stats:OptimizerStats;
	private var finalConstants:Array<Expr>;
	private var finalConstantIds:StringMap<Int>;

	public function new() {
		optimizationCache = new StringMap();
		exprHashes = new IntMap();
		stats = new OptimizerStats();
		finalConstants = [];
		finalConstantIds = new StringMap();
	}

	public function optimize(expr:Expr):Expr {
		if (!enabled) return expr;
		
		stats.reset();
		finalConstants = [];
		finalConstantIds = new StringMap();
		
		if (debug) {
			debugPrinter = new Printer();
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
		
		for (i in 0...optimizeLevel) {
			var passStart = haxe.Timer.stamp();
			
			var beforeHash = getExprHash(result);
			result = optimizeOnce(result);
			var afterHash = getExprHash(result);
			var passTime = (haxe.Timer.stamp() - passStart) * 1000;
			stats.totalPassTime += passTime;
			stats.passTimes.push(passTime);
			
			if (debug) {
				var optimizedCount = if (beforeHash != afterHash) "changed" else "unchanged";
				var afterStr = debugPrinter.exprToString(result);
				trace("\n--- Pass " + (i + 1) + " (" + passTime + " ms, " + optimizedCount + ") ---");
				trace(afterStr);
			}
			
			stats.totalPasses++;
			
			if (beforeHash == afterHash) {
				stats.skippedPasses++;
				if (debug) {
					trace("\n--- No changes in pass " + (i + 1) + ", stopping early ---");
				}
				break;
			}
		}
		
		stats.totalTime = stats.totalPassTime;
		
		if (debug) {
			trace("\n--- Optimization Complete ---");
			trace("Total passes: " + stats.totalPasses);
			trace("Skipped passes: " + stats.skippedPasses);
			trace("Total time: " + stats.totalTime + " ms");
			trace("Cache size: " + Lambda.count(optimizationCache));
			if (stats.totalPasses > 1) {
				trace("Average per pass: " + (stats.totalTime / stats.totalPasses) + " ms");
			}
			trace("=== End Debug ===\n");
		}
		
		return result;
	}

	private function getExprHash(expr:Expr):String {
		#if hscriptPos
		var id = expr.pmin;
		#else
		var id = expr.hashCode();
		#end
		
		if (exprHashes.exists(id)) {
			return exprHashes.get(id);
		}
		
		var hash = computeExprHash(expr);
		exprHashes.set(id, hash);
		return hash;
	}

	private function computeExprHash(expr:Expr):String {
		return switch (Tools.expr(expr)) {
			case EConst(c):
				"C:" + switch(c) {
					case CInt(v): "i" + v;
					case CFloat(f): "f" + f;
					case CString(s): "s" + s.length;
				}
			case EIdent(id): "I:" + id;
			case EPackage(name): "P:" + name;
			case EImport(c): "M:" + c;
			case EClass(name, fields, extend, interfaces, isFinal): 
				"CL:" + name + ":" + fields.length;
			case EVar(n, t, e, isPublic, isStatic, isPrivate, isFinal, isInline, get, set, isVar):
				"V:" + n + ":" + (e != null ? getExprHash(e) : "null");
			case EParent(e): "PR:" + getExprHash(e);
			case EBlock(exprs): 
				"B:[" + [for (e in exprs) getExprHash(e)].join(",") + "]";
			case EField(e, f, s):
				"FD:" + getExprHash(e) + ":" + f;
			case EBinop(op, e1, e2):
				"OP:" + op + ":" + getExprHash(e1) + ":" + getExprHash(e2);
			case EUnop(op, prefix, e):
				"UN:" + op + ":" + prefix + ":" + getExprHash(e);
			case ECall(e, params):
				"CLL:" + getExprHash(e) + ":[" + [for (p in params) getExprHash(p)].join(",") + "]";
			case EIf(cond, e1, e2):
				"IF:" + getExprHash(cond) + ":" + getExprHash(e1) + ":" + (e2 != null ? getExprHash(e2) : "null");
			case EWhile(cond, e):
				"WH:" + getExprHash(cond) + ":" + getExprHash(e);
			case EDoWhile(cond, e):
				"DW:" + getExprHash(cond) + ":" + getExprHash(e);
			case EFor(v, it, e, ithv):
				"FR:" + v + ":" + getExprHash(it) + ":" + getExprHash(e);
			case EBreak: "BR";
			case EContinue: "CT";
			case EFunction(args, e, name, ret, isPublic, isStatic, isOverride, isPrivate, isFinal, isInline):
				"FUN:" + name + ":" + getExprHash(e);
			case EReturn(e):
				"RET:" + (e != null ? getExprHash(e) : "null");
			case EArray(e, index):
				"ARR:" + getExprHash(e) + ":" + getExprHash(index);
			case EArrayDecl(exprs):
				"AD:[" + [for (e in exprs) getExprHash(e)].join(",") + "]";
			case ENew(cl, params, paramType):
				"NEW:" + cl + ":[" + [for (p in params) getExprHash(p)].join(",") + "]";
			case EThrow(e):
				"THR:" + getExprHash(e);
			case ETry(e, v, t, ecatch):
				"TRY:" + getExprHash(e) + ":" + getExprHash(ecatch);
			case EObject(fl):
				"OBJ:{" + [for (f in fl) f.name + ":" + getExprHash(f.e)].join(",") + "}";
			case ETernary(cond, e1, e2):
				"TRN:" + getExprHash(cond) + ":" + getExprHash(e1) + ":" + getExprHash(e2);
			case ESwitch(e, cases, defaultExpr):
				"SW:" + getExprHash(e) + ":[" + [for (c in cases) 
					"[" + [for (v in c.values) getExprHash(v)].join(",") + ":" + getExprHash(c.expr)
				].join(",") + "]:" + (defaultExpr != null ? getExprHash(defaultExpr) : "null");
			case EMeta(name, args, e):
				"MT:" + name + ":[" + (args != null ? [for (a in args) getExprHash(a)].join(",") : "") + "]:" + getExprHash(e);
			case ECheckType(e, t):
				"CT:" + getExprHash(e);
			case EEnum(en, isAbstract): "EN:" + en.name;
			case ECast(e, t): "CST:" + getExprHash(e);
			case ERegex(e, f): "RX:" + e;
		}
	}

	private function optimizeOnce(expr:Expr):Expr {
		return optimizeWithCache(expr, 0);
	}

	private function optimizeWithCache(expr:Expr, depth:Int):Expr {
		var useCache = !debug && depth < 3;
		var cacheKey = getCacheKey(expr);
		
		if (useCache && optimizationCache.exists(cacheKey)) {
			stats.cacheHits++;
			return optimizationCache.get(cacheKey);
		}
		
		stats.cacheMisses++;
		
		var result = switch (Tools.expr(expr)) {
			case EConst(_): 
				stats.constCount++;
				expr;
			case EIdent(_): 
				stats.identCount++;
				switch (Tools.expr(expr)) {
					case EIdent(id):
						var constId = finalConstantIds.get(id);
						if (constId != null) {
							stats.finalConstantReplacements++;
							return finalConstants[constId];
						}
					default:
				}
				expr;
			case EPackage(_): expr;
			case EImport(_): expr;
			case EClass(name, fields, extend, interfaces, isFinal):
				stats.classCount++;
				var optimizedFields = [for (f in fields) optimizeWithCache(f, depth + 1)];
				Tools.mk(EClass(name, optimizedFields, extend, interfaces, isFinal), expr);
			case EVar(n, t, e, isPublic, isStatic, isPrivate, isFinal, isInline, get, set, isVar):
				stats.varCount++;
				var optimizedExpr = e != null ? optimizeWithCache(e, depth + 1) : null;
				if (isFinal && optimizedExpr != null && isConstantExpr(optimizedExpr)) {
					var constId = finalConstants.length;
					finalConstants.push(optimizedExpr);
					finalConstantIds.set(n, constId);
				}
				Tools.mk(EVar(n, t, optimizedExpr, isPublic, isStatic, isPrivate, isFinal, isInline, get, set, isVar), expr);
			case EParent(e):
				stats.parentCount++;
				var optimized = optimizeWithCache(e, depth + 1);
				Tools.mk(EParent(optimized), expr);
			case EBlock(exprs):
				stats.blockCount++;
				var optimizedExprs = [for (e in exprs) optimizeWithCache(e, depth + 1)];
				var cleanedExprs = enableDeadCodeElimination ? removeDeadCode(optimizedExprs) : optimizedExprs;
				cleanedExprs = [for (e in cleanedExprs) switch (Tools.expr(e)) {
					case EVar(n, _, _, _, _, _, true, _, _, _, _):
						if (finalConstantIds.exists(n)) {
							stats.deadCodeEliminations++;
							continue;
						}
						e;
					default: e;
				}];
				if (cleanedExprs.length == 1) {
					cleanedExprs[0];
				} else {
					Tools.mk(EBlock(cleanedExprs), expr);
				}
			case EField(e, f, s):
				stats.fieldCount++;
				var optimized = optimizeWithCache(e, depth + 1);
				Tools.mk(EField(optimized, f, s), expr);
			case EBinop(op, e1, e2):
				stats.binopCount++;
				var optimized1 = optimizeWithCache(e1, depth + 1);
				var optimized2 = optimizeWithCache(e2, depth + 1);
				var folded = enableConstantFolding ? tryFoldConstant(op, optimized1, optimized2) : null;
				if (folded != null) {
					stats.folds++;
					folded;
				} else {
					var simplified = enableExpressionSimplification ? trySimplifyBinop(op, optimized1, optimized2) : null;
					if (simplified != null) {
						stats.simplifications++;
						simplified;
					} else if (optimized1 != e1 || optimized2 != e2) {
						Tools.mk(EBinop(op, optimized1, optimized2), expr);
					} else {
						expr;
					}
				}
			case EUnop(op, prefix, e):
				stats.unopCount++;
				var optimized = optimizeWithCache(e, depth + 1);
				var folded = enableConstantFolding ? tryFoldUnop(op, prefix, optimized) : null;
				if (folded != null) {
					stats.folds++;
					folded;
				} else {
					var simplified = enableExpressionSimplification ? trySimplifyUnop(op, prefix, optimized) : null;
					if (simplified != null) {
						stats.simplifications++;
						simplified;
					} else if (optimized != e) {
						Tools.mk(EUnop(op, prefix, optimized), expr);
					} else {
						expr;
					}
				}
			case ECall(e, params):
				stats.callCount++;
				var optimizedExpr = optimizeWithCache(e, depth + 1);
				var optimizedParams = [for (p in params) optimizeWithCache(p, depth + 1)];
				var paramsChanged = optimizedParams.length != params.length;
				if (!paramsChanged) {
					for (i in 0...params.length) {
						if (optimizedParams[i] != params[i]) {
							paramsChanged = true;
							break;
						}
					}
				}
				
				var callOptimized = tryOptimizeCall(optimizedExpr, optimizedParams);
				if (callOptimized != null) {
					stats.simplifications++;
					return callOptimized;
				}
				
				if (optimizedExpr != e || paramsChanged) {
					Tools.mk(ECall(optimizedExpr, optimizedParams), expr);
				} else {
					expr;
				}
			case EIf(cond, e1, e2):
				stats.ifCount++;
				var optimizedCond = optimizeWithCache(cond, depth + 1);
				var optimizedE1 = optimizeWithCache(e1, depth + 1);
				var optimizedE2 = e2 != null ? optimizeWithCache(e2, depth + 1) : null;
				
				var condOptimized = tryOptimizeCondition(optimizedCond);
				if (condOptimized != null) {
					optimizedCond = condOptimized;
				}
				
				if (enableBranchOptimization) {
					var optimized = tryOptimizeIf(optimizedCond, optimizedE1, optimizedE2);
					if (optimized != null) {
						stats.branchOptimizations++;
						optimized;
					} else if (optimizedCond != cond || optimizedE1 != e1 || optimizedE2 != e2) {
						Tools.mk(EIf(optimizedCond, optimizedE1, optimizedE2), expr);
					} else {
						expr;
					}
				} else if (optimizedCond != cond || optimizedE1 != e1 || optimizedE2 != e2) {
					Tools.mk(EIf(optimizedCond, optimizedE1, optimizedE2), expr);
				} else {
					expr;
				}
			case EWhile(cond, e):
				stats.whileCount++;
				var optimizedCond = optimizeWithCache(cond, depth + 1);
				var oldConstants = finalConstants.copy();
				var oldConstantIds = finalConstantIds.copy();
				var optimizedBody = optimizeWithCache(e, depth + 1);
				finalConstants = oldConstants;
				finalConstantIds = oldConstantIds;
				if (optimizedCond != cond || optimizedBody != e) {
					Tools.mk(EWhile(optimizedCond, optimizedBody), expr);
				} else {
					expr;
				}
			case EDoWhile(cond, e):
				stats.doWhileCount++;
				var oldConstants = finalConstants.copy();
				var oldConstantIds = finalConstantIds.copy();
				var optimizedCond = optimizeWithCache(cond, depth + 1);
				var optimizedBody = optimizeWithCache(e, depth + 1);
				finalConstants = oldConstants;
				finalConstantIds = oldConstantIds;
				if (optimizedCond != cond || optimizedBody != e) {
					Tools.mk(EDoWhile(optimizedCond, optimizedBody), expr);
				} else {
					expr;
				}
			case EFor(v, it, e, ithv):
				stats.forCount++;
				var optimizedIt = optimizeWithCache(it, depth + 1);
				var oldConstants = finalConstants.copy();
				var oldConstantIds = finalConstantIds.copy();
				var optimizedBody = optimizeWithCache(e, depth + 1);
				finalConstants = oldConstants;
				finalConstantIds = oldConstantIds;
				if (optimizedIt != it || optimizedBody != e) {
					Tools.mk(EFor(v, optimizedIt, optimizedBody, ithv), expr);
				} else {
					expr;
				}
			case EBreak: 
				stats.breakCount++;
				expr;
			case EContinue: 
				stats.continueCount++;
				expr;
			case EFunction(args, e, name, ret, isPublic, isStatic, isOverride, isPrivate, isFinal, isInline):
				stats.functionCount++;
				var oldConstants = finalConstants.copy();
				var oldConstantIds = finalConstantIds.copy();
				var optimizedBody = optimizeWithCache(e, depth + 1);
				finalConstants = oldConstants;
				finalConstantIds = oldConstantIds;
				if (optimizedBody != e) {
					Tools.mk(EFunction(args, optimizedBody, name, ret, isPublic, isStatic, isOverride, isPrivate, isFinal, isInline), expr);
				} else {
					expr;
				}
			case EReturn(e):
				stats.returnCount++;
				var optimized = e != null ? optimizeWithCache(e, depth + 1) : null;
				if (optimized != e) {
					Tools.mk(EReturn(optimized), expr);
				} else {
					expr;
				}
			case EArray(e, index):
				stats.arrayCount++;
				var optimizedExpr = optimizeWithCache(e, depth + 1);
				var optimizedIndex = optimizeWithCache(index, depth + 1);
				if (optimizedExpr != e || optimizedIndex != index) {
					Tools.mk(EArray(optimizedExpr, optimizedIndex), expr);
				} else {
					expr;
				}
			case EArrayDecl(exprs, wantedType):
				stats.arrayDeclCount++;
				var optimizedExprs = [for (e in exprs) optimizeWithCache(e, depth + 1)];
				var changed = optimizedExprs.length != exprs.length;
				if (!changed) {
					for (i in 0...exprs.length) {
						if (optimizedExprs[i] != exprs[i]) {
							changed = true;
							break;
						}
					}
				}
				if (changed) {
					Tools.mk(EArrayDecl(optimizedExprs, wantedType), expr);
				} else {
					expr;
				}
			case ENew(cl, params, paramType):
				stats.newCount++;
				var optimizedParams = [for (p in params) optimizeWithCache(p, depth + 1)];
				var changed = optimizedParams.length != params.length;
				if (!changed) {
					for (i in 0...params.length) {
						if (optimizedParams[i] != params[i]) {
							changed = true;
							break;
						}
					}
				}
				if (changed) {
					Tools.mk(ENew(cl, optimizedParams, paramType), expr);
				} else {
					expr;
				}
			case EThrow(e):
				stats.throwCount++;
				var optimized = optimizeWithCache(e, depth + 1);
				if (optimized != e) {
					Tools.mk(EThrow(optimized), expr);
				} else {
					expr;
				}
			case ETry(e, v, t, ecatch):
				stats.tryCount++;
				var optimizedTry = optimizeWithCache(e, depth + 1);
				var optimizedCatch = optimizeWithCache(ecatch, depth + 1);
				if (optimizedTry != e || optimizedCatch != ecatch) {
					Tools.mk(ETry(optimizedTry, v, t, optimizedCatch), expr);
				} else {
					expr;
				}
			case EObject(fl):
				stats.objectCount++;
				var optimizedFields = [for (f in fl) {name: f.name, e: optimizeWithCache(f.e, depth + 1)}];
				var changed = optimizedFields.length != fl.length;
				if (!changed) {
					for (i in 0...fl.length) {
						if (optimizedFields[i].e != fl[i].e) {
							changed = true;
							break;
						}
					}
				}
				if (changed) {
					var objectFields:Array<ObjectField> = [];
					for (f in optimizedFields) {
						objectFields.push({name: f.name, e: f.e});
					}
					Tools.mk(EObject(objectFields), expr);
				} else {
					expr;
				}
			case ETernary(cond, e1, e2):
				stats.ternaryCount++;
				var optimizedCond = optimizeWithCache(cond, depth + 1);
				var optimizedE1 = optimizeWithCache(e1, depth + 1);
				var optimizedE2 = optimizeWithCache(e2, depth + 1);
				
				if (enableBranchOptimization) {
					var optimized = tryOptimizeTernary(optimizedCond, optimizedE1, optimizedE2);
					if (optimized != null) {
						stats.branchOptimizations++;
						optimized;
					} else if (optimizedCond != cond || optimizedE1 != e1 || optimizedE2 != e2) {
						Tools.mk(ETernary(optimizedCond, optimizedE1, optimizedE2), expr);
					} else {
						expr;
					}
				} else if (optimizedCond != cond || optimizedE1 != e1 || optimizedE2 != e2) {
					Tools.mk(ETernary(optimizedCond, optimizedE1, optimizedE2), expr);
				} else {
					expr;
				}
			case ESwitch(e, cases, defaultExpr):
				stats.switchCount++;
				var optimizedExpr = optimizeWithCache(e, depth + 1);
				var optimizedCases = [for (c in cases) {
					values: [for (v in c.values) optimizeWithCache(v, depth + 1)],
					expr: optimizeWithCache(c.expr, depth + 1)
				}];
				var switchCases:Array<SwitchCase> = [];
				for (c in optimizedCases) {
					switchCases.push({values: c.values, expr: c.expr});
				}
				var optimizedDefault = defaultExpr != null ? optimizeWithCache(defaultExpr, depth + 1) : null;
				
				var changed = optimizedExpr != e || optimizedDefault != defaultExpr;
				if (!changed) {
					for (i in 0...cases.length) {
						var oldCase = cases[i];
						var newCase = optimizedCases[i];
						if (oldCase.values.length != newCase.values.length || oldCase.expr != newCase.expr) {
							changed = true;
							break;
						}
						for (j in 0...oldCase.values.length) {
							if (oldCase.values[j] != newCase.values[j]) {
								changed = true;
								break;
							}
						}
						if (changed) break;
					}
				}
				
				if (changed) {
					Tools.mk(ESwitch(optimizedExpr, switchCases, optimizedDefault), expr);
				} else {
					expr;
				}
			case EMeta(name, args, e):
				stats.metaCount++;
				var optimizedArgs = args != null ? [for (a in args) optimizeWithCache(a, depth + 1)] : null;
				var optimizedExpr = optimizeWithCache(e, depth + 1);
				var argsChanged = args != null && optimizedArgs.length == args.length;
				if (argsChanged) {
					for (i in 0...args.length) {
						if (optimizedArgs[i] != args[i]) {
							argsChanged = false;
							break;
						}
					}
				}
				if (optimizedExpr != e || (args != null && !argsChanged)) {
					Tools.mk(EMeta(name, optimizedArgs, optimizedExpr), expr);
				} else {
					expr;
				}
			case ECheckType(e, t):
				stats.checkTypeCount++;
				var optimized = optimizeWithCache(e, depth + 1);
				if (optimized != e) {
					Tools.mk(ECheckType(optimized, t), expr);
				} else {
					expr;
				}
			case EEnum(en, isAbstract): 
				stats.enumCount++;
				expr;
			case ECast(e, t):
				stats.castCount++;
				var optimized = optimizeWithCache(e, depth + 1);
				if (optimized != e) {
					Tools.mk(ECast(optimized, t), expr);
				} else {
					expr;
				}
			case ERegex(e, f): 
				stats.regexCount++;
				expr;
		}
		
		if (useCache) {
			optimizationCache.set(cacheKey, result);
		}
		
		return result;
	}

	private inline function getCacheKey(expr:Expr):String {
		#if hscriptPos
		return expr.pmin + ":" + expr.pmax;
		#else
		return Std.string(expr.hashCode());
		#end
	}

	public function clearCache():Void {
		optimizationCache = new StringMap();
		exprHashes = new IntMap();
		stats.cacheHits = 0;
		stats.cacheMisses = 0;
	}

	public function dispose():Void {
		optimizationCache = null;
		exprHashes = null;
		debugPrinter = null;
		stats = null;
	}

	public function getStats():OptimizerStats {
		return stats;
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
			case "!=":
				if (c1 != null && c2 != null) return makeConst(c1 != c2, e1);
				if (e1 == e2) return makeConst(false, e1);
			case "==":
				if (c1 != null && c2 != null) return makeConst(c1 == c2, e1);
				if (e1 == e2) return makeConst(true, e1);
			case ">":
				if (c1 != null && c2 != null) return makeConst(c1 > c2, e1);
			case "<":
				if (c1 != null && c2 != null) return makeConst(c1 < c2, e1);
			case ">=":
				if (c1 != null && c2 != null) return makeConst(c1 >= c2, e1);
			case "<=":
				if (c1 != null && c2 != null) return makeConst(c1 <= c2, e1);
			case "is":
				if (c1 != null && c2 != null) return makeConst(Std.isOfType(c1, c2), e1);
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
		
		if (op == "-") {
			var c = getConstValue(e);
			if (c != null) return makeConst(-c, e);
		}
		
		if (op == "+") return e;
		
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

	private function tryOptimizeCall(e:Expr, params:Array<Expr>):Null<Expr> {
		switch (Tools.expr(e)) {
			case EField({e: EIdent("Math")}, "abs"):
				if (params.length == 1) {
					var c = getConstValue(params[0]);
					if (c != null && c >= 0) return params[0];
					if (c != null) return makeConst(-c, params[0]);
				}
			case EField({e: EIdent("Math")}, "floor"):
				if (params.length == 1) {
					var c = getConstValue(params[0]);
					if (c != null) return makeConst(Math.floor(c), params[0]);
				}
			case EField({e: EIdent("Math")}, "ceil"):
				if (params.length == 1) {
					var c = getConstValue(params[0]);
					if (c != null) return makeConst(Math.ceil(c), params[0]);
				}
			case EField({e: EIdent("Math")}, "round"):
				if (params.length == 1) {
					var c = getConstValue(params[0]);
					if (c != null) return makeConst(Math.round(c), params[0]);
				}
			case EField({e: EIdent("Math")}, "sqrt"):
				if (params.length == 1) {
					var c = getConstValue(params[0]);
					if (c != null && c >= 0) return makeConst(Math.sqrt(c), params[0]);
				}
			case EField({e: EIdent("Math")}, "pow"):
				if (params.length == 2) {
					var c1 = getConstValue(params[0]);
					var c2 = getConstValue(params[1]);
					if (c1 != null && c2 != null) return makeConst(Math.pow(c1, c2), params[0]);
				}
			case EField({e: EIdent("Math")}, "sin"):
				if (params.length == 1) {
					var c = getConstValue(params[0]);
					if (c != null) return makeConst(Math.sin(c), params[0]);
				}
			case EField({e: EIdent("Math")}, "cos"):
				if (params.length == 1) {
					var c = getConstValue(params[0]);
					if (c != null) return makeConst(Math.cos(c), params[0]);
				}
			case EField({e: EIdent("Math")}, "tan"):
				if (params.length == 1) {
					var c = getConstValue(params[0]);
					if (c != null) return makeConst(Math.tan(c), params[0]);
				}
			case EField({e: EIdent("Math")}, "asin"):
				if (params.length == 1) {
					var c = getConstValue(params[0]);
					if (c != null) return makeConst(Math.asin(c), params[0]);
				}
			case EField({e: EIdent("Math")}, "acos"):
				if (params.length == 1) {
					var c = getConstValue(params[0]);
					if (c != null) return makeConst(Math.acos(c), params[0]);
				}
			case EField({e: EIdent("Math")}, "atan"):
				if (params.length == 1) {
					var c = getConstValue(params[0]);
					if (c != null) return makeConst(Math.atan(c), params[0]);
				}
			case EField({e: EIdent("Math")}, "log"):
				if (params.length == 1) {
					var c = getConstValue(params[0]);
					if (c != null && c > 0) return makeConst(Math.log(c), params[0]);
				}
			case EField({e: EIdent("Math")}, "PI"):
				return makeConst(Math.PI, e);
			case EField({e: EIdent("Math")}, "E"):
				return makeConst(2.718281828459045, e);
			case EField({e: EIdent("Std")}, "string"):
				if (params.length == 1) {
					var c = getConstValue(params[0]);
					if (c != null) return makeConst(Std.string(c), params[0]);
				}
			case EField({e: EIdent("Std")}, "int"):
				if (params.length == 1) {
					var c = getConstValue(params[0]);
					if (c != null) return makeConst(Std.int(c), params[0]);
				}
			case EField({e: EIdent("StringTools")}, "trim"):
				if (params.length >= 1) {
					var c = getConstValue(params[0]);
					if (c != null) return makeConst(StringTools.trim(c), params[0]);
				}
			default:
		}
		return null;
	}

	private function tryOptimizeCondition(cond:Expr):Null<Expr> {
		switch (Tools.expr(cond)) {
			case EIdent(id):
				var constId = finalConstantIds.get(id);
				if (constId != null) {
					return finalConstants[constId];
				}
			case EUnop("!", _, inner):
				switch (Tools.expr(inner)) {
					case EIdent(id):
						var constId = finalConstantIds.get(id);
						if (constId != null) {
							return Tools.mk(EUnop("!", false, finalConstants[constId]), cond);
						}
					case EUnop("!", _, inner2):
						return inner2;
					case EBinop("&&", a, b):
						return Tools.mk(EBinop("||", Tools.mk(EUnop("!", false, a), cond), 
							Tools.mk(EUnop("!", false, b), cond)), cond);
					case EBinop("||", a, b):
						return Tools.mk(EBinop("&&", Tools.mk(EUnop("!", false, a), cond), 
							Tools.mk(EUnop("!", false, b), cond)), cond);
					default:
				}
			default:
		}
		return null;
	}

	private inline function removeDeadCode(exprs:Array<Expr>):Array<Expr> {
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
	
	private inline function isUnconditionalTerminator(expr:Expr):Bool {
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

	private inline function getConstValue(expr:Expr):Null<Dynamic> {
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

	private inline function exprEquals(e1:Expr, e2:Expr):Bool {
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

	private inline function isPureConstant(expr:Expr):Bool {
		return switch (Tools.expr(expr)) {
			case EConst(_): true;
			case EParent(e): isPureConstant(e);
			default: false;
		}
	}

	private inline function isConstantExpr(expr:Expr):Bool {
		return switch (Tools.expr(expr)) {
			case EConst(_): true;
			case EParent(e): isConstantExpr(e);
			case EBinop(op, e1, e2): 
				var c1 = getConstValue(e1);
				var c2 = getConstValue(e2);
				c1 != null && c2 != null;
			case EUnop(op, prefix, e):
				getConstValue(e) != null;
			default: false;
		}
	}

	private inline function isStringExpr(expr:Expr):Bool {
		return switch (Tools.expr(expr)) {
			case EConst(CString(_)): true;
			case EParent(e): isStringExpr(e);
			case EBinop("+", e1, e2): isStringExpr(e1) || isStringExpr(e2);
			default: false;
		}
	}
	
	private inline function isPowerOfTwo(n:Float):Bool {
		if (n != Math.floor(n)) return false;
		var i = Std.int(n);
		if (i <= 0) return false;
		return (i & (i - 1)) == 0;
	}

}