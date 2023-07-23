
#[builtin]
fn builtin_wasm(data: IBytes) -> Result<ObjValue> {
    let engine = wasmtime::Engine::default();
    let data = sp_maybe_compressed_blob::decompress(
        data.as_ref(),
        sp_maybe_compressed_blob::CODE_BLOB_BOMB_LIMIT,
    )
    .unwrap();
    let module = wasmtime::Module::from_binary(&engine, data.as_ref())
        .map_err(|e| RuntimeError(format!("failed to create module: {e}").into()))?;
    for ele in module.exports() {
        dbg!(ele.name(), ele.ty());
    }
    for i in module.imports() {
        dbg!(i.module(),
        i.name());
    }

    #[derive(Default)]
    struct StoreData {
        memory: Option<Memory>,
        allocated: u32,
    }

    let mut store = wasmtime::Store::new(&engine, StoreData::default());
    
    let mut memory = Memory::new(&mut store, MemoryType::new(21, None)).unwrap();
    store.data_mut().memory = Some(memory);

    let mut instance = <Linker<StoreData>>::new(&engine);
    instance.func_new(
        "env",
        "ext_logging_max_level_version_1",
        FuncType::new([], [ValType::I32]),
        |caller, input, output| {
            output[0] = wasmtime::Val::I32(0);
            Ok(())
        },
    ).unwrap();
    instance.func_new(
        "env",
        "ext_allocator_malloc_version_1",
        FuncType::new([ValType::I32], [ValType::I32]),
        |mut caller, input, output| {
            let size: u32 = input[0].unwrap_i32().try_into().unwrap();
            let memory = caller.data().memory.unwrap();
            let allocated = caller.data().allocated;
            let new_allocated = allocated + size;
            while memory.data_size(&mut caller) < new_allocated as usize {
                memory.grow(&mut caller, 1).unwrap();
            }
            output[0] = wasmtime::Val::I32(allocated as i32);
            Ok(())
        },
    ).unwrap();
    // let print_hex = instance.func_new(
    //     "env",
    //     "ext_misc_print_utf8_version_1",
    //     FuncType::new([], []),
    //     |caller, input, output| {
    //         Ok(())
    //     },
    // ).unwrap();
    // let print_hex = instance.func_new(
    //     "env",
    //     "ext_misc_runtime_version_version_1",
    //     FuncType::new([], []),
    //     |caller, input, output| {
    //         Ok(())
    //     },
    // ).unwrap();
    //
    instance.define(&mut store, "env", "memory", memory).unwrap();
    instance.define_unknown_imports_as_traps(&module).unwrap();
    instance
        .module(&mut store, "runtime.wasm", &module)
        .unwrap();
    let instance = instance.instantiate(&mut store, &module).unwrap();
    let fun = instance
        .get_func(&mut store, "UniqueApi_token_data")
        .unwrap();
    let mut outputs = [wasmtime::Val::I32(0)];
    fun.call(&mut store, &[wasmtime::Val::I32(0), wasmtime::Val::I32(0)], &mut outputs).unwrap();
    todo!()
}
