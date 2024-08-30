module StackAlloc (Arch: Arch_full.Arch) : sig

  val memory_analysis :
    (Stack_alloc.sub_region -> string) ->
    (IInfo.t -> Stack_alloc.table -> Stack_alloc.region_map -> Stack_alloc.table * Stack_alloc.region_map) ->
    (Format.formatter -> Compiler_util.pp_error -> unit) ->
    debug:bool ->
    (Arch.reg, Arch.regx, Arch.xreg, Arch.rflag, Arch.cond, Arch.asm_op, Arch.extra_op) Arch_extra.extended_op Expr._uprog -> Compiler.stack_alloc_oracles

end
