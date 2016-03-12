scrypt
======

The [scrypt](https://en.wikipedia.org/wiki/Scrypt) password-base key derivation function (pkbdf) is an algorithm designed to be brute-force resistant that converts human readable passwords into fixed length arrays of bytes, which can then be used as a key for symetric block ciphers, private keys, et cetera.

### Features:
- **Non-blocking** - Gives other events in the event loop opportunities to run (asynchrorous)
- **Cancellable** - If the key is not longer required, the computation can be cancelled
- **Progress Callback** - Provides the current progress of key derivation as a percentage complete


Todo
----

These are all coming soon (as of 2016-03-12):
- Remove browser dependency on slow buffer
- Add test cases (from scrypt-async)


Tuning
------

The scrypt algorithm is, by design, expensive to execute, which increases the amount of time an attacker requires in order to brute force guess a password, adjustable by several parameters which can be tuned:
- **N** - The general work factor; increasing this increases the difficulty of the overall derivation
- **p** - The memory cost; increasing this increases the memory required during derivation
- **r** - The parallelization factor; increasing the computation required during derivation



Installing
----------

**node.js**

You should likely not use this module for *node.js* as there are many faster [alternatives](https://www.npmjs.com/package/scrypt), but if you so wish to do so:

```
npm install scrypt-js
```


**browser**

```html
<!-- This dependency will be removed soon -->
<script src="https://wzrd.in/standalone/buffer" type="text/javascript"></script>
        
<script src="https://raw.githubusercontent.com/ricmoo/scrypt-js/master/index.js" type="text/javascript"></script>
```

API
---

```html
<html>
  <body>
    <!-- These two libraries are highly recommended for encoding password/salt -->
    <script src="libs/buffer.js" type="text/javascript"></script>
    <script src="libs/unorm.js" type="text/javascript"></script>
    
    <!-- This shim library greatly improves performance of the scrypt algorithm -->
    <script src="libs/setImmediate.js" type="text/javascript"></script>

    <script src="index.js" type="text/javascript"></script>
    <script type="text/javascript">

      // See the section below: "Encoding Notes"
      var password = new buffer.SlowBuffer("anyPassword".normalize('NFKC'));
      var salt = new buffer.SlowBuffer("someSalt".normalize('NFKC'));

      var N = 1024, r = 8, p = 1;
      var dkLen = 32;
    
      scrypt(password, salt, N, r, p, dkLen, function(error, progress, key) {
        if (error) {
          console.log("Error: " + error);

        } else if (key) {
          console.log("Found: " + key);

        } else {
          // update UI with progress complete
          updateInterface(progress);
        }
      });
    </script>
  </body>
</html>
```

Encoding Notes
--------------

```
TL;DR - either only allow ASCII characters in passwords, or use
        String.prototype.normalize('NFKC') on any password
```

It is *HIGHLY* recommended that you do **NOT** pass strings into this (or any password-base key derivation function) library without careful consideration; you should convert your strings to a canonical format that you will use consistently across all platforms.

When encoding passowrds with UTF-8, it is important to realize that there may be multiple UTF-8 representations of a given string. Since the key generated by a password-base key derivation function is *dependant on the specific bytes*, this matters a great deal.

**Composed vs. Decomposed**

Certain UTF-8 code points can be combined with other characters to create composed characters. For example, the letter *a with the umlaut diacritic mark* (two dots over it) can be expressed two ways; as its composed form, U+00FC; or its decomposed form, which is the letter "u" followed by U+0308 (which basically means modify the previous character by adding an umlaut to it).

```javascript
// In the following two cases, a "u" with an umlaut would be seen
> '\u00fc'
> 'u\u0308'


// In its composed form, it is 2 bytes long
> new Buffer('u\u0308'.normalize('NFKC'))
<Buffer c3 bc>
> new Buffer('\u00fc')
<Buffer c3 bc>

// Whereas the decomposed form is 3 bytes, the letter u followed by U+0308
> new Buffer('\u00fc'.normalize('NFKD'))
<Buffer 75 cc 88>
> new Buffer('u\u0308')
<Buffer 75 cc 88>
```


**Compatibility equivalence mode**

Certain strings are often displayed the same, even though they may have different semantic means. For example, UTF-8 provides a code point for the roman number for one, which appears as the letter I, in most fonts identically. Compatibility equivalence will fold these two cases into simply the capital letter I.

```
> '\u2160'
'I'
> 'I'
'I'
> 'u2160' === 'I'
false
> '\u2160'.normalize('NFKC') === 'I'
true
```                                        


**Normalizing**

The `normalize()` method of a string can be used to convert a string to a specific form. Without going into too much detail, I generally recommend `NFKC`, however if you wish to dive deeper into this, a nice short summary can be found in Pythons [unicodedata module](https://docs.python.org/2/library/unicodedata.html#unicodedata.normalize)'s documentation.

For browsers without `normalize()` support, the [npm unorm module](https://www.npmjs.com/package/unorm) can be used to polyfill strings.


**Another example of encoding woes**

One quick story I will share is a project which used the `SHA256(encodeURI(password))` as a key, which (ignorig [raindbow table attacks](https://en.wikipedia.org/wiki/Rainbow_table)) had an unfortunate consequence of old web browsers replacing spaces with `+` while on new web browsers, replacing it with a `%20`, causing issues for anyone who used spaces in their password.


### Suggestions

- While it may be inconvenient to many international users, one option is to restrict passwords to a safe subset of ASCII, for example: `/^[A-Za-z0-9!@#$%^&*()]+$/`.
- My personal recommendation is to normalize to the NFKC form, however, one could imagine setting their password to a Chinese phrase on one computer, and then one day using a computer that does not have Chinese input capabilites and therefore be unable to log in.

**See:** [Unicode Equivalence](https://en.wikipedia.org/wiki/Unicode_equivalence)


Based On
--------

This code borrows **HEAVILY** from two other awesome <i>scrpt</i> libraries:
- **scryptsy** - This is the basis for this implementation of the base hashing algorithm
- **scrypt-async** - To remove the large dependency tree of pbkdf2 used in scryptsy, the custom (and highly performant) variant was used from this library


License
-------

MIT license.


References
----------

- [scrypt white paper](http://www.tarsnap.com/scrypt/scrypt.pdf)
- [wikipedia](https://en.wikipedia.org/wiki/Scrypt)
- [scrypt-async npm module](https://www.npmjs.com/package/scrypt-async)
- [scryptsy npm module](https://www.npmjs.com/package/scryptsy)
- [Unicode Equivalence](https://en.wikipedia.org/wiki/Unicode_equivalence)


Donations
---------

Obviously, it's all licensed under the MIT license, so use it as you wish; but if you'd like to buy me a coffee, I won't complain. =)

- Bitcoin - `1LsxZkCZpQXyiGsoAnAW9nRRfck3Nvv7QS`
- Dogecoin - `DF1VMTgyPsew619hwq5tT2RP8BNh2ZpzWA`
- Testnet3 - `muf7Vak4ZCVgtYZCnGStDXuoEdmZuo2nhA`
