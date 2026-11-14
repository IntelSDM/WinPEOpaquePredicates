@echo off

cd /d %~dp0

set SRC=Plugin.cpp WinPEOpaquePass.cpp
set OUT=build

if not exist "%OUT%" mkdir "%OUT%"

clang-cl  /LD /MD /I"C:\Users\dev\Desktop\llvm passes\llvm-project\LLVM-19.1.0-Windows-X64\include" /I"C:\Users\dev\Desktop\llvm passes\llvm-project\LLVM-19.1.0-Windows-X64\include" /I"C:\VCPKG\vcpkg\installed\x64-windows\include" /std:c++20 /O2 /Fo"%OUT%"\ %SRC% /link /DLL /LIBPATH:"C:\Users\dev\Desktop\llvm passes\llvm-project\LLVM-19.1.0-Windows-X64\lib" /LIBPATH:"C:\VCPKG\vcpkg\installed\x64-windows\lib" LLVMCore.lib LLVMSupport.lib LLVMAnalysis.lib LLVMTransformUtils.lib LLVMLinker.lib LLVMTextAPI.lib LLVMRemarks.lib LLVMObject.lib LLVMMCParser.lib LLVMBitReader.lib LLVMDebugInfoCodeView.lib LLVMDebugInfoMSF.lib LLVMBitstreamReader.lib LLVMTarget.lib LLVMTargetParser.lib LLVMMC.lib LLVMProfileData.lib LLVMIRReader.lib LLVMAsmParser.lib LLVMBinaryFormat.lib LLVMDemangle.lib LLVMipo.lib ntdll.lib winhttp.lib bcrypt.lib user32.lib gdi32.lib asmjit.lib asmtk.lib /out:"%OUT%\FunctionPass.dll" /IMPLIB:"%OUT%\FunctionPass.lib"

echo Build complete. Output: %OUT%\FunctionPass.dll
pause