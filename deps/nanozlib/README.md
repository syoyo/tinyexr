# nanoz

Nanoscale secure zlib decoding library utilizing wuffs `std/zlib`.

nanoz provides very limited zlib decoding functionalities.


## Advantages and disadvantages

* Advantage(s)
  * Born to be super secure.
    * No assert, No C++ exception. No segfault for corrupted/malcious zlib data.

* Disadvantage(s)
  * 50 KB or more in compiled binary(even compiled with `-Os`)

## Example

```
$ make
# 11 = uncompressed size
$ ./test_nanozdec test/test-000.txt.zz 11
```


## Wuffs version

v0.3.0

## TODO

* [ ] encoding(compress). wuffs doesn't provide zlib encoding feature at the moment.

## License

Apache 2.0

### Third party licenses

* wuffs. Apache 2.0. https://github.com/google/wuffs
