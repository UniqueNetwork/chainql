# chainql

Query Substrate blockchains using Jsonnet.

ChainQL is a utility for representing chain data in a JSON format and using Jsonnet to process and manipulate the output.
It is supposed to be a more convenient alternative to querying the chain data with PolkadotJS.

## Install

With [Rust](https://www.rust-lang.org/tools/install) installed, run
```bash
cargo install chainql
```
to install ChainQL globally. 

If you want to install and launch it locally, clone the repository and, in the repository, run
```bash
cargo build --release

./target/release/chainql
```

## Usage

To see all options, run

```bash
chainql --help
```

ChainQL operates on a `.jsonnet` file. With option `-e`, it can treat input as jsonnet code and evaluate it directly from the command line.

To supply a jsonnet function with arguments, use options from the **top level arguments** section of the help message, such as `--tla-str=${your arg name here}=${your arg value}` for a string, or `--tla-code=${arg name}=${your code}` for jsonnet code to be evaluated and the result passed as the value. Both strings and code can be supplied from files and environment (see **standard library** section of the help message), as well.

Inside the code, you can call `cql.${method name from the ones defined below}` for any built-in utility method defined in the ChainQL Rust code itself. These currently are:
```Rust
cql.chain(/* chain url to get the data from */)
cql.dump(/* chain metadata, dump data, optional parameters, to create a jsonnet representation of a mock chain storage */)
cql.toHex(/* array of bytes to convert to hex string */)
cql.fromHex(/* string to convert to an array of bytes */)
cql.calc(/* array of tokens to evaluate in postfix notation */)
cql.ss58(/* address to get the hex representation from */)
```

## Examples

*   ```bash
    chainql -e "(1 + 7) / 3"
    ```
    Option `-e` allows to run some jsonnet code from the input field and prints the result back into the terminal.

*   ```bash
    chainql -e "(import 'parachain-spec.json') {id+: '-local'}" > new-parachain-spec.json
    ```
    Applies `-local` to the value of the field `id` in the top field of some chain spec file. 
    The resulting file would look something like 
    ```json
    {
        "name": "some-parachain",
        "id": "parachain-id-local",
        // ...
    }
    ```

For examples with files and their usage, see the `examples` folder.