package hscript.macros;

import haxe.macro.Type.Ref;
#if macro
import haxe.macro.Type.ClassType;
import haxe.macro.Type.ModuleType;
import Type.ValueType;
import haxe.macro.Expr.Function;
import haxe.macro.Expr;
import haxe.macro.Type.MetaAccess;
import haxe.macro.Type.FieldKind;
import haxe.macro.Type.ClassField;
import haxe.macro.Type.VarAccess;
import haxe.macro.*;

using haxe.macro.ComplexTypeTools;
using haxe.macro.ExprTools;
using haxe.macro.TypeTools;
using StringTools;
using Lambda;

typedef ClassInfo = {
	var imports:Array<ImportExpr>;
	var ?params:Array<haxe.macro.Type.TypeParameter>;
}

@:nullSafety(Loose)
class CustomClassMacro {
	public static inline final FUNC_PREFIX = "_HX_SUPER__";
	public static inline final CLASS_SUFFIX = "_HSX";

	public static var unallowedMetas:Array<String> = [":bitmap", ":noCustomClass", ":generic"];
	private static var classesToBuild:Map<String, ClassInfo> = [];

	public static function init() {
		#if !display
		#if CUSTOM_CLASSES
		if (Context.defined("display"))
			return;
		for (apply in Config.ALLOWED_CUSTOM_CLASSES) {
			Compiler.addGlobalMetadata(apply, "@:build(hscript.macros.CustomClassMacro.fetchClass())");
		}
		Context.onAfterTyping(build);
		#end
		#end
	}

	public static function fetchClass():Array<Field> {
		var fields = Context.getBuildFields();
		var clRef = Context.getLocalClass();
		if (clRef == null)
			return fields;
		var cl = clRef.get();
		if (cl.isAbstract || cl.isExtern || cl.isFinal || cl.isInterface)
			return fields;
		if (!cl.name.endsWith("_Impl_") && !cl.name.endsWith(CLASS_SUFFIX) && !cl.name.endsWith("_HSC")) {
			var metas = cl.meta.get();

			for (m in metas)
				if (unallowedMetas.contains(m.name))
					return fields;

			// if(cl.params.length > 0)
			// 	return fields;

			var key = cl.module;
			var fkey = '${cl.module}.${cl.name}';
			if (key == "sys.thread.FixedThreadPool")
				return fields; // Error: Type name sys.thread.Worker_HSX is redefined from module sys.thread.FixedThreadPool
			if (key == "StdTypes")
				return fields; // Error: Cant extend basic class
			if (key == "Xml")
				return fields; // Error: Cant extend basic class
			if (key == "Date")
				return fields; // Error: Cant extend basic class
			if (key == "away3d.tools.commands.Mirror")
				return fields; // Error: Unknown identifier
			if (key == "away3d.tools.commands.SphereMaker")
				return fields; // Error: Unknown identifier
			if (key == "away3d.tools.commands.Weld")
				return fields; // Error: Unknown identifier
			if (fkey == "hscript.CustomClassHandler.TemplateClass")
				return fields; // Error: Redefined
			if (fkey == "hscript.CustomClassHandler.CustomTemplateClass")
				return fields; // Error: Redefined
			if (fkey == "hscript.CustomClass")
				return fields; // Error: Redefined
			if (key == "sys.thread.EventLoop")
				return fields; // Error: cant override force inlined
			if (Config.DISALLOW_CUSTOM_CLASSES.contains(key) || Config.DISALLOW_CUSTOM_CLASSES.contains(fkey))
				return fields;
			if (key.contains("_"))
				return fields;

			var imports = Context.getLocalImports().copy();
			for(imp in imports) {
				trace('$fkey');
				trace('import ${[for(i in imp.path) i.name].join(".")}');
				trace('\n');
			}
			var clsDecl:ClassInfo = {
				imports: imports,
				params: cl.params.length > 0 ? cl.params : null
			}

			classesToBuild.set(fkey, clsDecl);
		}
		return fields;
	}

	// called in an onAfterTyping callback
	public static function build(modules:Array<ModuleType>) {
		var classesToApply:Array<ClassType> = [];
		for (m in modules) {
			switch (m) {
				case TClassDecl(c):
					if (c == null)
						continue;
					var cl = c.get();
					var fkey = '${cl.module}.${cl.name}';
					if (classesToBuild.exists(fkey) /*&& classesToBuild.get(fkey).params == null*/) {
						classesToApply.push(cl);
					}
				/*
					if(cl.isAbstract || cl.isExtern || cl.isFinal || cl.isInterface) continue;
					if(!cl.name.endsWith("_Impl_") && !cl.name.endsWith(CLASS_SUFFIX) && !cl.name.endsWith("_HSC")) {
						var fkey = '${cl.module}.${cl.name}';
						if(classesToBuild.exists(fkey) && classesToBuild.get(fkey).params == null) {
							classesToApply.push(cl);
						} 
					}
				 */
				default:
			}
		}

		if (classesToApply.length > 0)
			buildClasses(classesToApply);
	}

	private static function buildClasses(classes:Array<ClassType>) {
		for (cl in classes)
			buildClass(cl);
	}

	private static function buildClass(cl:ClassType) {
		trace('building ${cl.module}.${cl.name} class');
		var classFields:Array<ClassField> = cl.fields.get();
		var classParams:Map<String, haxe.macro.Type> = [];
		if (cl.params.length != 0) {
			for (i => p in cl.params) {
				var pName = '${cl.pack.join(".")}.${cl.name}.${p.name}';
				var pFinalType = p.defaultType == null ? haxe.macro.Type.TDynamic(null) : p.defaultType;
				classParams.set(pName, pFinalType);
			}
		}

		var fields:Array<ClassField> = classFields.concat(getSuperFields(cl));

		var shadowClass:TypeDefinition = macro class {

		};

		trace('${cl.name} - setting shadowclass');

		shadowClass.kind = TDClass({
			pack: cl.pack.copy(),
			name: cl.name,
			params: cl.params.length == 0 ? null : [
				for (s => p in classParams)
					switch (p) {
						case TInst(_.get() => {kind: KExpr(e)}, _):
							TPExpr(e);
						default:
							TPType(FixedTypeTools.toComplexType(p));
					}
			]
		}, [
			{name: "IHScriptCustomClassBehaviour", pack: ["hscript"]}
		], false, true, false);
		shadowClass.name = '${cl.name}$CLASS_SUFFIX';
		var fkey = '${cl.module}.${cl.name}';
		var imports = classesToBuild.get(fkey).imports;
		if (imports != null) {
			setupMetas(shadowClass, imports, cl);
			processImport(imports, "hscript.utils.UnsafeReflect", "UnsafeReflect", cl.pos);
		}

		for(imp in imports) {
			trace('import ${[for(i in imp.path) i.name].join(".")}');
		}
		trace(new haxe.macro.Printer().printTypeDefinition(shadowClass));

		var definedFields:Array<String> = [];
		var hasNew:Bool = false;

		if (cl.constructor != null) {
			hasNew = true;
			var constField = cl.constructor.get();
			trace('${cl.name} - building constructor');
			switch (constField.type) {
				case TFun(args, ret):
					var constArgs:Array<FunctionArg> = [
						for (arg in args)
							{name: arg.name, opt: arg.opt, type: Context.toComplexType(arg.t)}
					];

					var constructor:Field = buildConstructor(constArgs, constField.pos);
					shadowClass.fields.push(constructor);
					definedFields.push(constField.name); // kinda redundant since is the constructor
				case TLazy(builder):
					var v = builder();
					switch (v) {
						case TFun(args, ret):
							var constArgs:Array<FunctionArg> = [
								for (arg in args)
									{name: arg.name, opt: arg.opt, type: Context.toComplexType(arg.t)}
							];

							var constructor:Field = buildConstructor(constArgs, constField.pos);
							shadowClass.fields.push(constructor);
							definedFields.push(constField.name);
						default:
					}
				default:
			}
		}

		trace('${cl.name} - overriding fields');
		for (f in fields) {
			if (f == null)
				continue;

			if (f.name.startsWith(FUNC_PREFIX))
				continue;
			if (f.isExtern || f.isFinal)
				continue;
			switch (f.kind) {
				case FMethod(k):
					switch (k) {
						case MethInline | MethDynamic | MethMacro: continue;
						default:
					}
				case FVar(_, _):
					continue;
			}

			if (f.name == "hget" || f.name == "hset")
				continue;
			if (definedFields.contains(f.name))
				continue;

			for (m in f.meta.get())
				if (unallowedMetas.contains(m.name))
					continue;

			switch (f.kind) {
				case FMethod(k):
					var newFields:Array<Field> = overrideField(f, cl, f.type, classParams);
					if(newFields.length == 0) continue;

					var overField:Field = newFields[0];
					var superField:Field = newFields[1];

					if (!overField.access.contains(AOverride))
						overField.access.push(AOverride);
					if (superField.access.contains(AOverride))
						superField.access.remove(AOverride);

					shadowClass.fields.push(overField);
					shadowClass.fields.push(superField);
					definedFields.push(f.name);
				default:
					// No :>
			}
		}

		if (definedFields.length == 0 && !hasNew) return;

		shadowClass.fields.push({
			name: "__cachedFieldSet",
			pos: cl.pos,
			kind: FVar(macro :Map<String, Dynamic>),
			access: [APublic, AStatic]
		});

		shadowClass.fields.push({
			name: "__interp",
			kind: FVar(macro :hscript.Interp),
			pos: cl.pos,
			access: [APublic]
		});

		shadowClass.fields.push({
			name: "__allowSetGet",
			pos: cl.pos,
			kind: FVar(macro :Bool, macro true),
			access: [APublic]
		});

		shadowClass.fields.push({
			name: "__real_fields",
			pos: cl.pos,
			kind: FVar(macro :Array<String>),
			access: [APublic]
		});

		shadowClass.fields.push({
			name: "__class__fields",
			pos: cl.pos,
			kind: FVar(macro :Array<String>),
			access: [APublic]
		});

		shadowClass.fields.push({
			name: "__callGetter",
			pos: cl.pos,
			kind: FFun({
				ret: macro :Dynamic,
				params: [],
				expr: macro {
					return null;
				},
				args: [
					{
						name: "name",
						opt: false,
						meta: [],
						type: macro :String
					}
				]
			}),
			access: [APublic]
		});

		shadowClass.fields.push({
			name: "__callSetter",
			pos: cl.pos,
			kind: FFun({
				ret: macro :Dynamic,
				params: [],
				expr: macro {
					return null;
				},
				args: [
					{
						name: "name",
						opt: false,
						meta: [],
						type: macro :String
					},
					{
						name: "val",
						opt: false,
						meta: [],
						type: macro :Dynamic
					}
				]
			}),
			access: [APublic]
		});

		if (cl.name == "FunkinShader" || cl.name == "CustomShader" || cl.name == "MultiThreadedScript") {
			Context.defineModule(cl.module, [shadowClass], imports);
			return;
		}

		var hasHgetInSuper = false;
		var hasHsetInSuper = false;

		// TODO: hget & hset

		for (f in fields) {
			if (f.name == "new")
				continue;
			if (f.name.startsWith(FUNC_PREFIX))
				continue;
			if (f.isExtern || f.isFinal)
				continue;
			switch (f.kind) {
				case FMethod(k):
					switch (k) {
						case MethInline | MethDynamic | MethMacro: continue;
						default:
					}
				case FVar(read, write):
					switch ([read, write]) {
						case [AccInline, AccInline]: continue;
						default:
					}
			}

			switch (f.type) {
				case TFun(args, ret):
					if (f.params != null && f.params.length > 0)
						continue;

					hasHgetInSuper = f.name == "hget";
					hasHsetInSuper = f.name == "hset";

					if (hasHgetInSuper && hasHsetInSuper)
						break;
				default:
			}
		}

		var hgetField = if (hasHgetInSuper) {
			macro {
				if (__interp != null) {
					if (__class__fields.contains(name)) {
						var v:Dynamic = __interp.variables.get(name);
						if (v != null && v is hscript.Property)
							return cast(v, hscript.Property).callGetter(name);
						return v;
					} else
						@:privateAccess {
						var cls:hscript.CustomClass = cast __interp.__customClass.__upperClass;
						while (cls != null) {
							if (cls.hasField(name))
								return cls.getField(name);

							var prev:hscript.CustomClass = cast cls.__upperClass;
							if (prev == null)
								break;
							cls = prev;
						}
					}
				}

				return super.hget(name);
			}
		} else {
			macro {
				if (__interp != null) {
					if (__class__fields.contains(name)) {
						var v:Dynamic = __interp.variables.get(name);
						if (v != null && v is hscript.Property)
							return cast(v, hscript.Property).callGetter(name);
						return v;
					} else
						@:privateAccess {
						var cls:hscript.CustomClass = cast __interp.__customClass.__upperClass;
						while (cls != null) {
							if (cls.hasField(name))
								return cls.getField(name);

							var prev:hscript.CustomClass = cast cls.__upperClass;
							if (prev == null)
								break;
							cls = prev;
						}
					}
				}

				return UnsafeReflect.getProperty(this, name);
			}
		}

		var hsetField = if (hasHsetInSuper) {
			macro {
				if (__interp != null) {
					if (__class__fields.contains(name)) {
						var v:Dynamic = __interp.variables.get(name);
						if (v != null && v is hscript.Property)
							return cast(v, hscript.Property).callSetter(name, val);
						__interp.variables.set(name, val);
						return val;
					} else
						@:privateAccess {
						var cls:hscript.CustomClass = cast __interp.__customClass.__upperClass;
						while (cls != null) {
							if (cls.hasField(name))
								return cls.setField(name, val);

							var prev:hscript.CustomClass = cast cls.__upperClass;
							if (prev == null)
								break;
							cls = prev;
						}
					}
				}

				if (__real_fields.contains(name)) {
					UnsafeReflect.setProperty(this, name, val);
					return UnsafeReflect.field(this, name);
				}
				return super.hset(name, val);
			}
		} else {
			macro {
				if (__interp != null) {
					if (__class__fields.contains(name)) {
						var v:Dynamic = __interp.variables.get(name);
						if (v != null && v is hscript.Property)
							return cast(v, hscript.Property).callSetter(name, val);
						__interp.variables.set(name, val);
						return val;
					} else
						@:privateAccess {
						var cls:hscript.CustomClass = cast __interp.__customClass.__upperClass;
						while (cls != null) {
							if (cls.hasField(name))
								return cls.setField(name, val);

							var prev:hscript.CustomClass = cast cls.__upperClass;
							if (prev == null)
								break;
							cls = prev;
						}
					}
				}

				if (__real_fields.contains(name)) {
					UnsafeReflect.setProperty(this, name, val);
					return UnsafeReflect.field(this, name);
				}
				// __custom__variables.set(name, val);
				return val;
			}
		}

		shadowClass.fields.push({
			name: "hset",
			pos: cl.pos,
			access: hasHsetInSuper ? [AOverride, APublic] : [APublic],
			kind: FFun({
				ret: macro :Dynamic,
				params: [],
				expr: hsetField,
				args: [
					{
						name: "name",
						opt: false,
						meta: [],
						type: macro :String
					},
					{
						name: "val",
						opt: false,
						meta: [],
						type: macro :Dynamic
					}
				]
			})
		});

		shadowClass.fields.push({
			name: "hget",
			pos: cl.pos,
			access: hasHgetInSuper ? [AOverride, APublic] : [APublic],
			kind: FFun({
				ret: macro :Dynamic,
				params: [],
				expr: hgetField,
				args: [
					{
						name: "name",
						opt: false,
						meta: [],
						type: macro :String
					}
				]
			})
		});

		/*
			var p = new Printer();
			var aa = p.printTypeDefinition(shadowClass);
			trace('\n');
			trace(aa);
		 */

		Context.defineModule(cl.module, [shadowClass], imports);
	}

	// Based on Polymod HScriptClass Macro: https://github.com/larsiusprime/polymod/blob/develop/polymod/hscript/_internal/HScriptedClassMacro.hx#L686
	private static function overrideField(field:ClassField, cl:ClassType, ?type:haxe.macro.Type, ?params:Map<String, haxe.macro.Type>):Array<Field> {
		if (type == null)
			type = field.type;

		switch (type) {
			case TLazy(f):
				var fv = f();
				return overrideField(field, cl, fv, params);
			case TFun(args, ret):
				for (a in args)
					switch (a.t) {
						case TInst(t, p):
							var tp = t.get();
							if (tp != null && tp.isPrivate) return [];
						default:
					}
				// Inline functions are already skipped
				// As well for "@:generic" fields

				var fnInputArgs:Array<FunctionArg> = [];

				// We only get limited information about the args from Type, we need to use TypedExprDef.

				// Is failing here
				var fieldExpr:Null<haxe.macro.Type.TypedExpr> = field.expr();
				if (fieldExpr == null)
					return [];

				var fnAccess:Array<Access> = [field.isPublic ? APublic : APrivate];
				if (field.isFinal)
					fnAccess.push(AFinal);

				switch (fieldExpr.expr) {
					case TFunction(tfunc):
						for (arg in tfunc.args) {
							var opt:Bool = (arg.value != null);
							var fnMeta:Metadata = arg.v.meta.get();
							var fnExpr:Null<Expr> = !opt ? null : Context.getTypedExpr(arg.value);
							// The argument type. We have to handle any type parameters, and deparameterizeType does so recursively.
							var fnType:ComplexType = Context.toComplexType(deparameterizeType(arg.v.t, params));

							var fnArg:FunctionArg = {
								name: arg.v.name,
								type: fnType,
								value: fnExpr,
								meta: fnMeta
							};

							fnInputArgs.push(fnArg);
						}
					case TConst(_):
						// This is actually a VARIABLE storing a function.
						return [];
					default:
				}

				// TODO

				var returnsVoid:Bool = ret.toString() == "Void";

				var fnCall:Array<Expr> = [for (a in args) macro $i{a.name}];
				var fnParams:Array<TypeParamDecl> = [for (fp in field.params) {name: fp.name}];
				var fnRet:Null<ComplexType> = returnsVoid ? null : Context.toComplexType(deparameterizeType(ret, params));
				var fnName:String = field.name;

				var overField:Field = {
					name: fnName,
					access: fnAccess,
					pos: field.pos,
					meta: field.meta.get(),
					kind: FFun({
						args: fnInputArgs,
						params: fnParams,
						ret: fnRet,
						expr: macro {
							var name:String = $v{fnName};

							if (__interp != null && __class__fields.contains(name)) {
								var v:Dynamic = null;
								if (Reflect.isFunction(v = __interp.variables.get(name))) {
									${
										!returnsVoid ? (macro return v($a{fnCall})) : macro {
											v($a{fnCall});
											return;
										}
									}
								}
							}

							${
								!returnsVoid ? (macro return super.$fnName($a{fnCall})) : (macro super.$fnName($a{fnCall}))
							}
						}
					})
				}

				var superFunField:Field = {
					name: '$FUNC_PREFIX${fnName}',
					pos: field.pos,
					access: [APrivate],
					meta: field.meta.get(),
					kind: FFun({
						args: fnInputArgs,
						params: fnParams,
						ret: fnRet,
						expr: macro {
							${
								!returnsVoid ? (macro return super.$fnName($a{fnCall})) : (macro super.$fnName($a{fnCall}))
							}
						}
					})
				}

				return [overField, superFunField];

			/* case TInst(_, _): return [];
				case TEnum(_, _): return [];
				case TMono(_): return [];
				case TAnonymous(_): return [];
				case TDynamic(_): return [];
				case TAbstract(_, _): return []; */
			default:
		}
		return [];
	}

	static function getBaseParamsOfType(parentType:haxe.macro.Type, paramTypes:Array<haxe.macro.Type>):Array<haxe.macro.Type.TypeParameter> {
		var parentParams:Array<haxe.macro.Type.TypeParameter> = [];

		switch (parentType) {
			case TMono(t):
				var ty = t.get();
				return getBaseParamsOfType(ty, paramTypes);

			case TInst(t, params):
				// Continue
				parentParams = t.get().params;

			case TType(t, params):
				// Recurse
				var ty:haxe.macro.Type = t.get().type;
				return getBaseParamsOfType(ty, paramTypes);

			case TDynamic(t):
				// Recurse
				return getBaseParamsOfType(t, paramTypes);

			case TLazy(f):
				// Recurse
				var ty:haxe.macro.Type = f();
				return getBaseParamsOfType(ty, paramTypes);

			case TAbstract(t, _params):
				// Continue
				parentParams = t.get().params;

			// case TEnum(t:Ref<EnumType>, params:Array<Type>):
			// case TFun(args:Array<{name:String, opt:Bool, t:Type}>, ret:Type):
			// case TAnonymous(a:Ref<AnonType>):
			default:
				// Context.error('Unsupported type: ${parentType}', Context.currentPos());
		}

		var result:Array<haxe.macro.Type.TypeParameter> = [];

		for (i => parentParam in parentParams) {
			var newParam:haxe.macro.Type.TypeParameter = {
				name: parentParam.name,
				t: paramTypes[i],
			};
			result.push(newParam);
		}

		return result;
	}

	static function scanBaseTypes(type:haxe.macro.Type):Array<haxe.macro.Type> {
		switch (type) {
			case TFun(args, ret):
				var results:Array<haxe.macro.Type> = [];

				for (result in scanBaseTypes(ret)) {
					results.push(result);
				}
				for (arg in args) {
					for (result in scanBaseTypes(arg.t)) {
						results.push(result);
					}
				}
				return results;
			case TAbstract(ty, params):
				if (params.length == 0) {
					return [type];
				} else {
					var results:Array<haxe.macro.Type> = [];
					for (param in params) {
						for (result in scanBaseTypes(param)) {
							results.push(result);
						}
					}
					return results;
				}
			default:
				return [type];
		}
	}

	static function deparameterizeType(targetType:haxe.macro.Type, targetParams:Map<String, haxe.macro.Type>):haxe.macro.Type {
		var resultType:haxe.macro.Type = targetType;

		switch (targetType) {
			case TFun(args, ret):
				// Function type.
				// This is not referring to functions of a class, but rather a function taken as a parameter (like a callback).

				// Deparameterize the return type.
				var retType:haxe.macro.Type = deparameterizeType(ret, targetParams);
				// Deparameterize the argument types.
				var argTypes:Array<{name:String, opt:Bool, t:haxe.macro.Type}> = args.map(function(arg) {
					return {
						name: arg.name,
						opt: arg.opt,
						t: deparameterizeType(arg.t, targetParams),
					};
				});

				// Construct the new type.
				resultType = TFun(argTypes, retType);

			case TAbstract(ty, params):
				// Abstract type. Sometimes used by types like Null<T>.

				var name = ty.toString();
				var typ = ty.get();

				// Check if the Abstract type is a parameter we recognize and can replace.
				if (targetParams.exists(ty.toString())) {
					// If so, replace it with the real type.
					resultType = targetParams.get(ty.toString());
					// recursive call in case result is a parameter
					resultType = deparameterizeType(resultType, targetParams);
				} else if (params.length != 0) {
					var oldParams:Array<haxe.macro.Type> = [];
					var newParams:Array<haxe.macro.Type> = [];
					for (param in params) {
						var baseTypes = scanBaseTypes(param);

						for (baseType in baseTypes) {
							var newParam = deparameterizeType(baseType, targetParams);
							if (newParam.toString() != "Void") {
								oldParams.push(baseType);
								newParams.push(newParam);
							}
						}
					}
					var baseParams = getBaseParamsOfType(resultType, oldParams);
					newParams = newParams.slice(0, baseParams.length);

					if (newParams.length > 0) {
						// Context.info('Building new abstract (${baseParams} + ${newParams})...', Context.currentPos());
						resultType = resultType.applyTypeParameters(baseParams, newParams);
						// Context.info('Deparameterized abstract type: ${resultType.toString()}', Context.currentPos());
					}
				}
			case TInst(ty, params):
				// Instance type. Used by most variables.

				// Check if the Instance type is a parameter we recognize and can replace.
				if (targetParams.exists(ty.toString())) {
					// If so, replace it with the real type.
					resultType = targetParams.get(ty.toString());
					// recursive call in case result is a parameter
					resultType = deparameterizeType(resultType, targetParams);
				} else if (params.length != 0) {
					var oldParams:Array<haxe.macro.Type> = [];
					var newParams:Array<haxe.macro.Type> = [];
					for (param in params) {
						var baseTypes = scanBaseTypes(param);

						for (baseType in baseTypes) {
							var newParam = deparameterizeType(baseType, targetParams);
							if (newParam.toString() != "Void") {
								oldParams.push(baseType);
								newParams.push(newParam);
							}
						}
					}
					var baseParams = getBaseParamsOfType(resultType, oldParams);
					newParams = newParams.slice(0, baseParams.length);

					if (newParams.length > 0) {
						// Context.info('Building new abstract (${baseParams} + ${newParams})...', Context.currentPos());
						resultType = resultType.applyTypeParameters(baseParams, newParams);
						// Context.info('Deparameterized abstract type: ${resultType.toString()}', Context.currentPos());
					} else {
						// Leave the type as is.
					}
				}

			default:
				// Do nothing.
				// Muted because I haven't actually seen any issues caused by this. Maybe investigate in the future.
		}

		return resultType;
	}

	private static function getSuperFields(cl:ClassType):Array<ClassField> {
		var fields:Array<ClassField> = [];
		var superClsRef = cl.superClass;
		while (superClsRef != null) {
			var superCls:ClassType = superClsRef.t.get();
			fields = fields.concat(superCls.fields.get());
			var next = superCls.superClass;
			if (next == null)
				break;
			superClsRef = next;
		}

		return fields;
	}

	private static function buildConstructor(args:Array<FunctionArg>, pos:Position):Field {
		var superCallArgs:Array<Expr> = [for (arg in args) macro $i{arg.name}];

		return {
			name: 'new',
			access: [APublic],
			pos: pos,
			kind: FFun({
				args: args,
				expr: macro {
					// Call the super constructor with appropriate args
					super($a{superCallArgs});

					if (__cachedFieldSet != null) {
						for (k => v in __cachedFieldSet) {
							Reflect.setProperty(this, k, v);
						}
						__cachedFieldSet.clear();
						__cachedFieldSet = null;
					}
				}
			}),
		}
	}

	// Grabbed from Utils.hx
	static function setupMetas(shadowClass:TypeDefinition, imports:Array<ImportExpr>, cl:ClassType) {
		shadowClass.meta = [
			{
				name: ":dox",
				params: [macro hide],
				pos: cl.pos
			},
			{
				name: ":noCompletion",
				params: [],
				pos: cl.pos
			}
		];
		var module = Context.getModule(cl.module);
		for (m in module)
			switch (m) {
				case TInst(t, params):
					if (t == null)
						continue;
					var ty = t.get();
					processModule(shadowClass, ty.module, ty.name, cl.pos);
					processImport(imports, ty.module, ty.name, cl.pos);
				case TEnum(t, params):
					if (t == null)
						continue;
					var ty = t.get();
					processModule(shadowClass, ty.module, ty.name, cl.pos);
					processImport(imports, ty.module, ty.name, cl.pos);
				case TType(t, params):
					if (t == null)
						continue;
					var ty = t.get();
					processModule(shadowClass, ty.module, ty.name, cl.pos);
					processImport(imports, ty.module, ty.name, cl.pos);
				case TAbstract(t, params):
					if (t == null)
						continue;
					var ty = t.get();
					processModule(shadowClass, ty.module, ty.name, cl.pos);
					processImport(imports, ty.module, ty.name, cl.pos);
				default:
			}
	}

	static function processImport(imports:Array<ImportExpr>, module:String, n:String, pos:Position) {
		if (n.endsWith("_Impl_"))
			n = n.substr(0, n.length - 6);
		module = fixModuleName(module);
		if (module.endsWith("_Impl_"))
			module = module.substr(0, module.length - 6);

		imports.push({
			path: [
				for (m in module.split("."))
					{
						name: m,
						pos: pos
					}
			],
			mode: INormal
		});
	}

	static function processModule(shadowClass:TypeDefinition, module:String, n:String, pos:Position) {
		if (n.endsWith("_Impl_"))
			n = n.substr(0, n.length - 6);
		if (module.endsWith("_Impl_"))
			module = module.substr(0, module.length - 6);

		shadowClass.meta.push({
			name: ':access',
			params: [
				Context.parse(fixModuleName(module.endsWith('.${n}') ? module : '${module}.${n}'), pos)
			],
			pos: pos
		});
	}

	static function fixModuleName(name:String):String {
		return [for (s in name.split(".")) if (s.charAt(0) == "_") s.substr(1) else s].join(".");
	}
}
#else
class CustomClassMacro {
	public var usedClass:Class<Dynamic>;
	public var className:String;
}
#end
