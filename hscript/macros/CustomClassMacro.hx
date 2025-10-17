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

using StringTools;
using Lambda;

@:nullSafety(Loose)
class CustomClassMacro {
    public static inline final FUNC_PREFIX = "_HX_SUPER__";
	public static inline final CLASS_SUFFIX = "_HSX";

	public static var unallowedMetas:Array<String> = [":bitmap", ":noCustomClass", ":generic"];
	private static var classImports:Map<String, Array<ImportExpr>> = [];

    public static function init() {
		#if !display
		#if CUSTOM_CLASSES
		if(Context.defined("display")) return;
		for(apply in Config.ALLOWED_CUSTOM_CLASSES) {
			//Compiler.addGlobalMetadata(apply, "@:build(hscript.macros.CustomClassMacro.fetchImports())");
		}
		//Context.onAfterTyping(buildTyped);
		#end
		#end
	}

	public static function fetchImports():Array<Field> {
		var fields = Context.getBuildFields();
		var clRef = Context.getLocalClass();
		if (clRef == null) return fields;
		var cl = clRef.get();
		if (cl.isAbstract || cl.isExtern || cl.isFinal || cl.isInterface) return fields;
		if (!cl.name.endsWith("_Impl_") && !cl.name.endsWith(CLASS_SUFFIX) && !cl.name.endsWith("_HSC")) {
			var key = cl.module;
			var fkey = '${cl.module}.${cl.name}';
			if (Config.DISALLOW_CUSTOM_CLASSES.contains(key) || Config.DISALLOW_CUSTOM_CLASSES.contains(fkey))
				return fields;
			if (key.contains("_"))
				return fields;
			
			var imports = Context.getLocalImports().copy();
			classImports[fkey] = imports;
		}
		return fields;
	}

    public static function build(modules:Array<ModuleType>) {
        var classesToApply:Array<ClassType> = [];
		for(m in modules) {
			switch(m) {
				case TClassDecl(c):
					if(c == null) continue;
					var cl = c.get();
					if(cl.isAbstract || cl.isExtern || cl.isFinal || cl.isInterface) continue;
					if(!cl.name.endsWith("_Impl_") && !cl.name.endsWith(CLASS_SUFFIX) && !cl.name.endsWith("_HSC")) {
						var key = cl.module;
						var fkey = '${cl.module}.${cl.name}';
						if(Config.DISALLOW_CUSTOM_CLASSES.contains(key) || Config.DISALLOW_CUSTOM_CLASSES.contains(fkey)) continue;
						if(key.contains("_")) continue;
						var isValid = Config.ALLOWED_CUSTOM_CLASSES.exists((s:String) -> return fkey.startsWith(s) || key.startsWith(s));
						if (isValid) {
							classesToApply.push(cl);
						}
					}
				default:
			}
		}

		if(classesToApply.length > 0) buildClasses(classesToApply);
    }

	private static function buildClasses(classes:Array<ClassType>)  {
		for(cl in classes) 
			buildClass(cl);
	}

	private static function buildClass(cl:ClassType) {
		var classFields:Array<ClassField> = cl.fields.get();
		var fields:Array<ClassField> = classFields.concat(getSuperFields(cl));

		var shadowClass:TypeDefinition = macro class {

		};

		var definedFields:Array<String> = [];
		var hasNew:Bool = false;

		for(f in fields) {
			if(f == null) continue;

			if(f.name == "new") {
				hasNew = true;
				switch(f.type) {
					case TFun(args, ret):
						// TODO: constructor
						var constArgs:Array<FunctionArg> = [
							for (arg in args)
								{name: arg.name, opt: arg.opt, type: Context.toComplexType(arg.t)}
						];

						var constructor:Field = buildConstructor(constArgs, f.pos);
						shadowClass.fields.push(constructor);
						definedFields.push(f.name);
					case TLazy(builder):
						var v = builder();
						switch(v) {
							case TFun(args, ret):
								var constArgs:Array<FunctionArg> = [
									for (arg in args)
										{name: arg.name, opt: arg.opt, type: Context.toComplexType(arg.t)}
								];

								var constructor:Field = buildConstructor(constArgs, f.pos);
								shadowClass.fields.push(constructor);
								definedFields.push(f.name);
							default:
								continue;
						}
					default: 
						continue;
				}
				continue;
			}
			if(f.name.startsWith(FUNC_PREFIX))
				continue;
			if(f.isExtern || f.isFinal) 
				continue;
			switch(f.kind) {
				case FMethod(k):
					switch (k) {
						case MethInline | MethDynamic | MethMacro: continue;
						default:
					}
				case FVar(read, write):
					switch([read, write]) {
						case [AccInline, AccInline]: continue;
						default:
					}
			}
			
			if(f.name == "hget" || f.name == "hset") continue;
			if(definedFields.contains(f.name)) continue;

			for(m in f.meta.get())
				if(unallowedMetas.contains(m.name))
					continue;

			switch (f.kind) {
				case FMethod(k):
					var newFields = overrideField(f, cl);

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

		if(definedFields.length == 0 && !hasNew) 
			return;
		
		shadowClass.kind = TDClass({
			pack: cl.pack.copy(),
			name: cl.name
		}, [
			{name: "IHScriptCustomClassBehaviour", pack: ["hscript"]}
		], false, true, false);
		
		var fkey = '${cl.module}.${cl.name}';
		var imports = classImports[fkey];
		if(imports != null) {
			Utils.setupMetas(shadowClass, imports);
			Utils.processImport(imports, "hscript.utils.UnsafeReflect", "UnsafeReflect");
		}

		shadowClass.fields.push({
			name: "__interp",
			kind: FVar(macro: hscript.Interp),
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

		if(cl.name == "FunkinShader" || cl.name == "CustomShader" || cl.name == "MultiThreadedScript") {
			Context.defineModule(cl.module, [shadowClass], null);
			return;
		}

		var hasHgetInSuper = false;
		var hasHsetInSuper = false;

		// TODO: hget & hset

		for(f in fields) {
			if(f.name == "new") continue;
			if(f.name.startsWith(FUNC_PREFIX)) continue;
			if(f.isExtern || f.isFinal) continue;
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

			switch(f.type) {
				case TFun(args, ret):
					if(f.params != null && f.params.length > 0) continue;

					hasHgetInSuper = f.name == "hget";
					hasHsetInSuper = f.name == "hset";

					if(hasHgetInSuper && hasHsetInSuper)
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

		Context.defineModule(cl.module, [shadowClass], null);
	}

	private static function overrideField(field:ClassField, cl:ClassType, ?type:haxe.macro.Type):Array<Field> {
		if(type == null)
			type = field.type;

		switch(type) {
			case TLazy(f):
				var fv = f();
				return overrideField(field, cl, fv);
			case TFun(args, ret):
				for (a in args)
					switch (a.t) {
						case TInst(t, p):
							var tp = t.get();
							if (tp != null && tp.isPrivate) return [];
					}
				// Inline functions are already skipped
				// As well for "@:generic" fields

				var inputArgs:Array<FunctionArg> = [];

				if(field.expr() == null) return [];

				var fnAccess:Array<Access> = [field.isPublic ? APublic : APrivate];

				switch(field.expr().expr) {
					case TFunction(tfunc):
						for(arg in tfunc.args) {

						}
					case TConst(_):
						return [];
					default:
				}

				// TODO

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

	private static function getSuperFields(cl:ClassType):Array<ClassField> {
		var fields:Array<ClassField> = [];
		var superClsRef = cl.superClass;
		while(superClsRef != null) {
			var superCls:ClassType = superClsRef.t.get();
			fields = fields.concat(superCls.fields.get());
			var next = superCls.superClass;
			if(next == null)
				break;
			superClsRef = next;
		}
		
		return fields;
	}

	private static function buildConstructor(args:Array<FunctionArg>, pos):Field {
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
				}
			}),
		}
	}
}
#else
class CustomClassMacro {
    public var usedClass:Class<Dynamic>;
	public var className:String;
}
#end