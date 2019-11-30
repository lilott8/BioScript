# ChemStor
An SMT-based solution for safely storing and disposing of chemicals.

## Disclaimer

This is research-grade code.
While CheStor does have strong mathematical guarantees, the supporting code is intended as an artifact for the accompanying paper.
In short: use at your own risk, we are not responsible for any negative consequences of using this code in the current form it resides in.

We acknowledge that the input and output is arcane and difficult to decipher.
We are working to make this easier to use, and easier to understand the output.

## Usage

usage: 
```
main.py [-h] -i INPUT [-d] [-wd WORKING_DIRECTORY] [-o OUTPUT]
               [-validate] [-epa EPA_DEFS] [-abs ABS_INT] [--dbname DBNAME]
               [--dbuser DBUSER] [--dbpass DBPASS] [--dbaddr DBADDR]
               [--dbdriver {odbc,mysql}]
```

### Optional Arguments:

| Short             | Long                  | Flag                                      | Purpose                                               |
| ------------------|-----------------------|-------------------------------------------|-------------------------------------------------------|
| -h                | --help                |                                           | show this help message and exit                       |
| -i                | --input               | path/to/input.bs                          | Location of input file                                |
| -d                | --debug               |                                           | Enable debugging.                                     |
| -o                | --output              | path/to/output/dir                        | Enable writing output. Must be set to write anything  |
| -wd               | --working-directory   | path/to/directory                         | Directory from where you wish to work                 |
| -epa              | --epa-defs            | Path/to/epa_defs.json         | Location of the EPA definition file (default: `./resources/epa.json`)                         |
| -abs              | --abs-int             | path/to/abs-int.txt           | Location of the abstract interaction file (default: `./resources/abstract-interaction.txt`)   |
| -validate         | --validate            |                                           | Only provide a boolean `True` or `False` for the problem instance |

### DB*:
**Database specific arguments**

| Flag              | Argument      | Purpose                                   |
|-------------------|---------------|-------------------------------------------|
| --dbname          | str           | Name of database.                         |
| --dbuser          | str           | Database user.                            |
| --dbpass          | str           | Database password for user.               |
| --dbaddr          | {IP, Host}    | Address of database.                      |
| --dbdriver        | {mysql,odbc}  | Database driver.                          |

\* The database options aren't really used here.

## Setup

Please see the installation page for [BioScript](https://github.com/lilott8/BioScript)

## Example Usages

We now provide a few simple cases detailing ChemStor's ability to correctly identify a valid storage solution and notify the user that a valid solution doesn't exists.

### Valid Solution
Provide a simple input: `simple_test.json`:

```python path/to/BioScript/storage/main.py -i resources/chemstor/simple_test.json```

This particular test will emit the following:

 `{
    'locations': [(0, 0)], 
    'chemicals': [
        volume_of_Ammonium Hydrosulfide_0 = 0,
        color_of_Ammonium Hydrosulfide_0 = 0
    ]
 }`
 
 This is to say, that all input is capable of being stored in the same cabinet on the same shelf.
 There are only two chemicals and one cabinet in this simple example.
 Both are given the "color" of `0`, meaning they are safe should they interact.
 The output only states that `Ammonium Hydrosulfide` is safe to store in the cabinet given (as there is only one cabinet).  
 
 ### No Possible Solution
 
 Provide a simple input: `methanol_nitric_acid.json`:
 
 ```python /path/to/BioScript/storage/main.py -i resources/chemstor/methanol_nitric_acid.json```
 
 This particular test will emit the following:
 
 ```
ChemStore couldn't find a safe, valid solution.
``` 

 Which is to say that given the constraints, ChemStor couldn't find any configuration that safely stores the input.
 ### Additional Tests:
 
 [BioScript's resource directory](https://github.com/lilott8/BioScript/tree/master/resources/chemstor) houses the rest of the test cases we use. 