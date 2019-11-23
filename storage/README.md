# ChemStor
An SMT-based solution for safely storing and disposing of chemicals.

##Usage

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

Provide a simple input: `simple_test.json` and this is ready to go.

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
 