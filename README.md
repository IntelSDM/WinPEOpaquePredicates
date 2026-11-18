# WinPE Opaque predicates
Built for LLVM 19.1 - Windows x64 <br> <br>

To be very clear, you must have ASLR support/Relocations on for this pass to work! <br>
This is only for usermode too! <br>
This pass takes known components to the windows PE and kernel structure to make reliable predicates:<br>

* TEB Start Addresses
* PEB Start Addresses
* IAT/EAT Addresses
* Fake Import/Export Look ups to impossible hashes
* Using known Import/Export Look ups to known hashes
* Image bases
* Heap limits
* PEB Module Walk to impossible or known modules
* Address sanitization(Using known upper and lower bounds into a hash, certain values are impossible/ others are always present)

We then use these opaque values to make multi purpose truth tables. <br>
This forces you to first of all know everything about the loaded binary which breaks symbolic execution, know the truth inputs due to the hashing which breaks AI. <br>
Since they are fully based around runtime constants set by windows, you can't break them with a lifter. <br>
Forcing runtime analysis. <br>
If you have something like a build server, or custom packer; you can also use other more precise opaque predicates of the same variety. 

<img width="1073" height="727" alt="image" src="https://github.com/user-attachments/assets/71912b16-f55b-4a0f-920b-236719f25356" /> <br>
<img width="1299" height="951" alt="image" src="https://github.com/user-attachments/assets/b0e6e931-c591-414e-923a-277b4a5514fc" /> <br>
<img width="1297" height="972" alt="image" src="https://github.com/user-attachments/assets/c9764403-6a7d-4d0a-98f0-888a9c477a61" /> <br>
<img width="966" height="941" alt="image" src="https://github.com/user-attachments/assets/cb8cd0de-5c4e-4aa7-9b00-baa7f4c4cfa4" /> <br>
<img width="1144" height="958" alt="image" src="https://github.com/user-attachments/assets/f5f4cb87-8af0-4a9b-b090-dc9ca7dae82c" /> <br>
<img width="1385" height="904" alt="image" src="https://github.com/user-attachments/assets/543b1b19-e2dc-4d15-ad5a-305707df2e85" /> <br>


## Annotations
```c
__attribute__((annotate("obfus")))
``` 
* Marks your function for the pass

## How To Build
* Download [LLVM 19.1](https://github.com/llvm/llvm-project/releases/tag/llvmorg-19.1.0)
* Download [VCPKG](https://github.com/microsoft/vcpkg)
* VCPKG install asmjit
* Open build.bat in a text editor.
* Find the LLVM 19.1 references in the command line, Change them to your file path.
* Find the VCPKG references in the command line, Change them to your file path.
* Run the build script
* Build your application with the ``` -load-pass-plugin ``` Param to the FunctionPass.dll

 
