

import os
import subprocess
from subprocess import PIPE
import hashlib

from pexpect import spawn, EOF, TIMEOUT

class Murphi(object):
    def __init__(self, name, mu_path, mu_include, gxx_path, mu_file_dir, mu_ctx,
        memory=10240, timeout=600):
        super(Murphi, self).__init__()
        self.name = hashlib.md5(name).hexdigest()
        self.mu_path = mu_path
        self.mu_include = mu_include
        self.gxx_path = gxx_path
        self.mu_file_dir = mu_file_dir
        self.mu_ctx = mu_ctx
        self.memory = memory
        self.timeout = timeout

    def check(self, inv):
        mu_file = self.gen_mu_file(inv)
        cpp_file = self.mu_compile(mu_file)
        exe_file = self.cpp_compile(cpp_file)
        return 'false' if self.expect_fail(exe_file) else 'true'

    def gen_mu_file(self, inv):
        if not os.path.isdir(self.mu_file_dir):
            os.makedirs(self.mu_file_dir)
        filename = os.path.join(self.mu_file_dir, self.name + '.m')
        with open(filename, 'w') as f:
            f.write(self.mu_ctx)
            f.write('\ninvariant "to check"\n%s;\n'%inv)
        return filename

    def mu_compile(self, filename):
        subprocess.call([self.mu_path, filename], stderr=PIPE, stdout=PIPE)
        return os.path.join(self.mu_file_dir, self.name + '.cpp')

    def cpp_compile(self, filename):
        exe_file = os.path.join(self.mu_file_dir, self.name)
        subprocess.call([self.gxx_path, filename, '-I', self.mu_include, '-o', exe_file],
            stderr=PIPE, stdout=PIPE)
        return exe_file

    def expect_fail(self, filename):
        process = spawn(filename + ' -pn -m %d'%self.memory)
        res = process.expect(['Invariant\s+".*?"\s+failed.', EOF, TIMEOUT], timeout=self.timeout)
        process.terminate(force=True)
        os.remove(os.path.join(self.mu_file_dir, self.name + '.m'))
        os.remove(os.path.join(self.mu_file_dir, self.name + '.cpp'))
        os.remove(os.path.join(self.mu_file_dir, self.name))
        return res == 0




if __name__ == '__main__':
    ctx = ''
    with open('mutualEx.m', 'r') as f:
        ctx = f.read()
    mu = Murphi('mutualEx',
        '/home/duan/Downloads/cmurphi5.4.9/src/mu',
        '/home/duan/Downloads/cmurphi5.4.9/include',
        '/usr/bin/g++',
        '/tmp/cmurphi/',
        ctx,
        memory=1024,
    )
    print mu.check('!(n[1] = C & n[2] = C)')

