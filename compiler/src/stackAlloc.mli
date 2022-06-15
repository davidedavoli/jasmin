module StackAlloc (Arch: Arch_full.Arch) : sig

  val memory_analysis :
    (Stack_alloc.sub_region -> char list) ->
    (Format.formatter -> Compiler_util.pp_error -> unit) ->
    debug:bool ->
      (IInfo.t -> Stack_alloc.table * Stack_alloc.Region.region_map ->
            Stack_alloc.table * Stack_alloc.Region.region_map) ->
    (Arch.reg, Arch.regx, Arch.xreg, Arch.rflag, Arch.cond, Arch.asm_op, Arch.extra_op) Arch_extra.extended_op Expr._uprog -> Compiler.stack_alloc_oracles

end
