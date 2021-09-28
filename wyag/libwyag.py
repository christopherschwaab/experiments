#!/usr/bin/env python3

# https://wyag.thb.lt/

from typing import cast, List, Optional, OrderedDict, TypeVar, Union

import argparse
import collections
import configparser
import hashlib
import os
import re
import struct
import sys
import zlib

StrPath = Union[str, os.PathLike[str]]

class GitRepo():
    """A git repository"""

    worktree: StrPath
    gitdir: StrPath

    def __init__(self, path: StrPath, force: bool=False) -> None:
        self.worktree = path
        self.gitdir = os.path.join(path, '.git')

        if not (force or os.path.isdir(self.gitdir)):
            raise Exception('Not a git repository {}'.format(path))

        self.conf = configparser.ConfigParser()
        cf = repo_file(self, "config")

        if cf and os.path.exists(cf):
            self.conf.read([cf])
        elif not force:
            raise Exception('Configuration file missing')

        if not force:
            vers = int(self.conf.get('core', 'repositoryformatversion'))
            if vers != 0:
                raise Exception('Unsupported repositoryformatversion {}'.format(vers))

def repo_path(repo: GitRepo, *path: StrPath) -> StrPath:
    """Compute path under repo's gitdir."""
    return os.path.join(repo.gitdir, *path)

def repo_file(repo: GitRepo, *path: StrPath, mkdir: bool=False) -> Optional[StrPath] :
    """Same as repo_path, but create dirname(*path) if absent. For example,
repo_file(r, "refs", "remotes", "origin", "HEAD") will create
.git/refs/remotes/origin."""
    if repo_dir(repo, *path[:-1], mkdir=mkdir):
        return repo_path(repo, *path)

def repo_dir(repo: GitRepo, *path: StrPath, mkdir: bool=False) -> Optional[StrPath]:
    """Same as repo_path, but mkdir *path if absent if mkdir."""
    rpath = repo_path(repo, *path)

    if os.path.exists(rpath):
       if os.path.isdir(rpath):
           return rpath
       else:
           raise Exception('Not a directory {}'.format(path))

    if mkdir:
        os.makedirs(rpath)
        return rpath
    else:
        return None

T = TypeVar('T')
def ensure(x: Optional[T]) -> T:
    assert(x is not None)
    return x

def repo_create(path):
    """Create a new repository at path."""

    repo = GitRepo(path, True)

    if os.path.exists(repo.worktree):
        if not os.path.isdir(repo.worktree):
            raise Exception('{} is not a directory!'.format(path))
        if os.listdir(repo.worktree):
            raise Exception('{} is not empty!'.format(path))

    assert(repo_dir(repo, 'branches', mkdir=True))
    assert(repo_dir(repo, 'objects', mkdir=True))
    assert(repo_dir(repo, 'refs', 'tags', mkdir=True))
    assert(repo_dir(repo, 'refs', 'heads', mkdir=True))

    # .git/description
    with open(ensure(repo_file(repo, 'description')), 'w') as f:
        f.write('Unnamed repository; edit this file "description" to name the repository.\n')

    # .git/HEAAD
    with open(ensure(repo_file(repo, 'HEAD')), 'w') as f:
        f.write('refs: refs/heads/master\n')

    return repo

def repo_default_config():
    ret = configparser.ConfigParser()

    ret.add_section('core')
    ret.set('core', 'repositoryformatversion', '0')
    ret.set('core', 'filename', 'false')
    ret.set('core', 'bare', 'false')

    return ret

def repo_find(path: StrPath='.', required: bool=True) -> Optional[GitRepo]:
    path = os.path.realpath(path)

    if os.path.isdir(os.path.join(path, '.git')):
        return GitRepo(path)

    parent = os.path.realpath(os.path.join(path, '..'))

    if parent == path:
        if required:
            raise Exception('No git directory.')
        else:
            return None

    return repo_find(parent, required)

class GitObject():
    repo: GitRepo
    ty: bytes

    def __init__(self, repo: GitRepo, data=None):
        self.repo = repo

        if data is not None:
            self.deserialize(data)

    def serialize(self) -> bytes:
        """This function MUST be implemented by subclasses.

It must read the object's contents from self.data, a byte string, and do
whatever it takes to convert it into a meaningful representation. What exactly
that means depend on each subclass."""
        raise Exception("Unimplemented!")

    def deserialize(self, data):
        raise Exception("Unimplemented!")

def parse_object(obj: bytes, sha: str) -> GitObject:
    size_ix = obj.find(b' ')
    ty = obj[0:size_ix]

    contents_ix = obj.find(b'\x00', size_ix)
    size = int(obj[size_ix:contents_ix].decode('ascii'))

    if size != len(obj) - size_ix - 1:
        raise Exception('Malformed object {0}: bad length'.format(sha))

    contents = obj[contents_ix+1:]
    try:
        return {
            b'commit': lambda: GitCommit(repo, contents),
            b'tree': lambda: GitTree(repo, contents),
            b'tag': lambda: GitTag(repo, contents),
            b'blob': lambda: GitBlob(repo, contents)
        }[ty]()
    except KeyError:
        raise Exception('Unknown type {0} for object {1}'.format(ty.decode("ascii"), sha))

def object_read(repo: GitRepo, sha: str) -> GitObject:
    """Read object object_id from Git repository repo. Return a GitObject whose
    exact type depends on the object."""
    path = repo_file(repo, 'objects', sha[0:2], sha[2:])
    if path is None:
        raise Exception('the required directory ".git/objects" does not exists!')

    with open(path, 'rb') as f:
        return parse_object(zlib.decompress(f.read()), sha)

def object_resolve(repo: GitRepo, name: str) -> Optional[List[str]]:
    """Resolve name to an object hash in repo.

This function is aware of:

 - the HEAD literal
 - short and long hashes
 - tags
 - branches
 - remote branches"""
    candidates = list()
    hashRe = re.compile(r'^[0-9A-Fa-f]{4,40}$')

    if not name.strip():
        return None

    if name == 'HEAD':
        return [ref_resolve(repo, 'HEAD')]

    if hashRe.match(name):
        # Unambiguous hash.
        if len(name) == 40:
            return [name.lower()]

        # Collect all candidates prefixed by hash/name.
        name = name.lower()
        prefix = name[0:2]
        path = repo_dir(repo, 'objects', prefix, mkdir=False)
        if path:
            rem = name[2:]
            for f in os.listdir(path):
                if f.startswith(rem):
                    candidates.append(prefix + f)

    return candidates

def object_find(repo: GitRepo, name: str, ty: Optional[bytes]=None, follow: bool=True):
    shas = object_resolve(repo, name)

    if not shas:
        raise Exception('No sucg reference{}.'.format(name))

    if len(shas) > 1:
        raise Exception('Ambiguous reference {}, candidates are:\n - {}.'.format(name, '\n - '.join(shas)))

    sha = shas[0]
    if not ty:
        return sha

    while True:
        obj = object_read(repo, sha)
        if obj.ty == ty:
            return sha

        if not follow:
            return None

        if type(obj) is GitTag:
            sha = obj.fields[b'object'].decode('ascii')
        elif type(obj) is GitCommit:
            sha = obj.fields[b'tree'].decode('ascii')
        elif type(obj) is GitTree:
            sha = obj.entries[b'tree'].decode('ascii')
        else:
            return None

def object_write(obj: GitObject, actually_write: bool=True):
    contents = obj.serialize()
    encoded_obj = obj.ty + b' ' + str(len(contents)).encode() + b'\x00' + contents
    sha = hashlib.sha1(encoded_obj).hexdigest()

    print('encoded object of type {} with length {} is: {}'.format(obj.ty, len(contents), encoded_obj))

    if actually_write:
        path = repo_file(obj.repo, 'objects', sha[0:2], sha[2:], mkdir=actually_write)
        if path is None:
            raise Exception('the path ".git/objects/" does not exist!')

        with open(path, 'wb') as f:
            f.write(zlib.compress(encoded_obj))

    return sha

class GitBlob(GitObject):
    blobdata: Optional[bytes]

    ty = b'blob'

    def serialize(self):
        return self.blobdata

    def deserialize(self, data: bytes):
        self.blobdata = data

def object_hash(fd, ty: str, repo: Optional[GitRepo]=None):
    data = fd.read()

    obj = {
        b'commit': lambda: GitCommit(repo, data),
        b'tree': lambda: GitTree(repo, data),
        b'tag': lambda: GitTag(repo, data),
        b'blob': lambda: GitBlob(repo, data),
    }[ty]()
    return object_write(obj, repo is not None)

def kvlm_parse(obj: bytes, start: int=0, fields: Optional[OrderedDict]=None):
    fields = fields or collections.OrderedDict()

    space_ix = obj.find(b' ', start)
    newline_ix = obj.find(b'\n', start)

    # Blank line => remainder of data is the message
    if space_ix < 0 or newline_ix < space_ix:
        assert(newline_ix == start)
        fields[b''] = obj[start+1]
        return fields

    field = obj[start:space_ix]

    end = start
    while True:
        end = obj.find(b'\n', end+1)
        if obj[end+1] != ord(' '):
            break

    value = obj[space_ix+1:end].replace(b'\n', b'\n')

    if field in fields:
        if type(fields[field]) == list:
            fields[field].append(value)
        else:
            fields[field] = [fields[field], value]
    else:
        fields[field] = value

    return kvlm_parse(obj, start=end+1, fields=fields)

def kvlm_serialize(fields):
    ret = b''

    for field in fields.keys():
        if field == b'':
            continue

        val = fields[field]
        if type(val) != list:
            val = [val]

        for v in val:
            ret += field + b' ' + v.replace(b'\n', b'\n') + b'\n'

    ret += b'\n' + fields[b'']

    return ret

class GitCommit(GitObject):
    ty = b'commit'

    def deserialize(self, data: bytes):
        self.fields = kvlm_parse(data)

    def serialize(self):
        self.fields = kvlm_serialize(self.fields)

class GitTreeLeaf(object):
    def __init__(self, mode: str, path: StrPath, sha: str):
        self.mode = mode
        self.path = path
        self.sha = sha

def tree_parse_entry(obj: bytes, start: int=0):
    mode_end_ix = obj.find(b' ', start)
    assert(mode_end_ix - start == 5 or mode_end_ix - start == 6)

    mode = obj[start:mode_end_ix].decode('ascii')

    path_end_ix = obj.find(b'\x00', mode_end_ix)
    path = obj[mode_end_ix+1:path_end_ix].decode('ascii')

    sha = hex(int.from_bytes(obj[path_end_ix+1:path_end_ix+21], 'big'))[2:]

    return path_end_ix+21, GitTreeLeaf(mode, path, sha)

def tree_parse(obj: bytes):
    pos = 0
    max = len(obj)
    entries = list()
    while pos < max:
        pos, entry = tree_parse_entry(obj, pos)
        entries.append(entry)
    return entries

class GitTree(GitObject):
    ty = b'tree'

    def deserialize(self, data):
        self.entries = tree_parse(data)

    def serialize(self):
        return tree_serialize(self)

def tree_serialize(obj: GitTree):
    encoded_entries = b''
    for entry in obj.entries:
        encoded_entries += entry.mode
        encoded_entries += b' '
        encoded_entries += entry.path
        encoded_entries += b'\x00'
        sha = int(entry.sha, 16)
        encoded_entries += sha.to_bytes(20, byteorder='big')
    return encoded_entries

def parse_cli(args):
    argparser = argparse.ArgumentParser(description='The stupid content tracker.')
    argsubparsers = argparser.add_subparsers(title='Commands', dest='command')

    argsp = argsubparsers.add_parser('init', help='Initialise a new, empty repository.')
    argsp.add_argument('path', metavar='directory', nargs='?', default='.', help='Where to create the repository.')

    argsp = argsubparsers.add_parser('cat-fie', help='Provide content of repository objects.')
    argsp.add_argument('type',
                       metavar='type',
                       choices=['blob', 'commit', 'tag', 'tree'],
                       help='Specify the type.')
    argsp.add_argument('object', metavar='object', help='The object to display.')

    argsp = argsubparsers.add_parser('hash-object', help='Compute object ID and optionally creates a blob from a file.')
    argsp.add_argument('-t',
                       metavar='type',
                       dest='type',
                       choices=['blob', 'commit', 'tag', 'tree'],
                       default='blob',
                       help='Specify the type')
    argsp.add_argument('-w',
                       dest='write',
                       action='store_true',
                       help='Actually write the object into the database.')
    argsp.add_argument('path', help='Read object from <file>.')

    argsp = argsubparsers.add_parser('log', help='Display history of a given commit.')
    argsp.add_argument('commit',
                       default='HEAD',
                       nargs='?',
                       help='Commit to start at.')

    argsp = argsubparsers.add_parser('checkout', help='Checkout a commit inside of a directory.')
    argsp.add_argument('commit', help='The commit or tree to checkout.')
    argsp.add_argument('path', help='The EMPTY directory to checkout on.')

    argsp = argsubparsers.add_parser('show-ref', help='List references.')

    argsp = argsubparsers.add_parser('tag', help='List and create tags.')
    argsp.add_argument('-a',
                       action='store_true',
                       dest='create_tag_object',
                       help='Whether to create a tag object.')
    argsp.add_argument('name',
                       nargs='?',
                       help="The new tag's name.")
    argsp.add_argument('object',
                       default='HEAD',
                       nargs='?',
                       help='The object the new tag will point to.')

    argsp = argsubparsers.add_parser('rev-parse', help='Parse revision (or other objects) identifiers.')
    argsp.add_argument('--wyag-type',
                       metavar='type',
                       dest='type',
                       choices=['blob', 'commit', 'tag', 'tree'],
                       default=None,
                       help='Specify the expected type.')
    argsp.add_argument('name', help='The name to parse.')

    argsubparsers.required = True

    return argparser.parse_args(args)

def cmd_add(args):
    raise NotImplementedError()

def cmd_cat_file(args):
    repo = repo_find()
    if repo is None:
        raise Exception('no repository found!')
    cat_file(repo, args.object, ty=args.type.encode())

def cat_file(repo: GitRepo, name: str, ty: str=None):
    obj = object_read(repo, object_find(repo, obj, ty=ty))
    sys.stdout.buffer.write(obj.serialize())

def cmd_checkout(args):
    repo = repo_find()
    assert(repo is not None)

    obj = object_read(repo, object_find(repo, args.commit))
    if type(obj) is GitCommit:
        obj = object_read(repo, obj.fields[b'tree'].decode('ascii'))

    assert(type(obj) is GitTree)
    if os.path.exists(args.path):
        if not os.path.isdir(args.path):
            raise Exception('Not a directory {}!'.format(args.path))
        if os.listdir(args.path):
            raise Exception('Not empty {}!'.format(args.path))
    else:
        os.makedirs(args.path)

    tree_checkout(repo, obj, os.path.realpath(args.path).encode())

def tree_checkout(repo: GitRepo, tree: GitTree, path: StrPath):
    for entry in tree.entries:
        obj = object_read(repo, entry.sha)
        dest = os.path.join(path, entry.path)

        if type(obj) is GitTree:
            os.mkdir(dest)
            tree_checkout(repo, obj, dest)
        elif type(obj) is GitBlob and obj.blobdata:
            with open(dest, 'wb') as f:
                f.write(obj.blobdata)

def ref_resolve(repo: GitRepo, ref: str) -> str:
    ref_file = repo_file(repo, ref)
    assert(ref_file is not None)
    with open(ref_file, 'r') as fp:
        data = fp.read()[:-1]
    if data.startswith('ref: '):
        return ref_resolve(repo, data[5:])
    else:
        return data

RefList = OrderedDict[str, Union['RefList', str]]
def ref_list(repo: GitRepo, path: StrPath=None) -> RefList:
    if not path:
        path = ensure(repo_dir(repo, 'refs'))

    refs = collections.OrderedDict()
    for f in sorted(os.listdir(path)):
        can = os.path.join(path, f)
        if os.path.isdir(can):
            refs[f] = ref_list(repo, can)
        else:
            refs[f] = ref_resolve(repo, can)

    return refs

class GitTag(GitCommit):
    ty = b'tag'

class GitIndexEntry():
    ctime = None
    """The last time a file's metadata changed.  This is a tuple (seconds, nanoseconds)."""

    mtime = None
    """The last time a file's data changed.  This is a tuple (seconds, nanoseconds)."""

    dev = None
    """The ID of device containing this file."""
    ino = None
    """The file's inode number."""
    mode_type = None
    """The object type, either b1000 (regular), b1010 (symlink), or b1110 (gitlink)."""
    mode_perms = None
    """The object permissions, an integer."""
    uid = None
    """User ID of owner."""
    gid = None
    """Group ID of owner (according to stat 2)"""
    size = None
    """Size of this object, in bytes."""
    obj = None
    """The object's hash as a hex string."""
    flag_assume_valid = None
    flag_extended = None
    flag_stage = None
    flag_name_length = None
    """Length of the name if < 0xfff, -1 otherwise"""

    name = None

# https://github.com/git/git/blob/master/Documentation/technical/index-format.txt
def parse_index_entry(obj: bytes, start: int=0) -> tuple[int, str, GitIndexEntry]:
    struct.unpack(
        'IIIIIIIIIIII',
        obj)

def parse_index(obj: bytes) -> OrderedDict[str, GitIndexEntry]:
    if obj[:4] != b'DIRC':
        raise Exception('index file missing magic head "DIRC".')
    version = obj[4:8]
    entry_count = int.from_bytes(obj[8:12], 'big')

    entries = collections.OrderedDict()
    for _ in range(entry_count):
        pos, name, entry = parse_index_entry(obj, pos)
        entries[name] = entry

    return entries

def cmd_commit(args):
    raise NotImplementedError()

def cmd_hash_object(args):
    repo = GitRepo('.') if args.write else None
    with open(args.path, 'rb') as fd:
        print(object_hash(fd, args.type.encode(), repo))

def cmd_init(args):
    repo_create(args.path)

def cmd_log(args):
    repo = repo_find()
    assert(repo is not None)

    print('digraph wyalog{')
    log_graphviz(repo, object_find(repo, args.commit), set())
    print('}')

def log_graphviz(repo: GitRepo, sha: str, seen: set):
    if sha in seen:
        return
    seen.add(sha)

    commit = object_read(repo, sha)
    if type(commit) is not GitCommit:
        raise Exception('encountered non commit while dumping')

    if not b'parent' in commit.fields.keys():
        return

    parents = commit.fields[b'parent']

    if type(parents) is not list:
        parents = [parents]

    for p in parents:
        p = p.decode('ascii')
        print('c_{} -> c_{};'.format(sha, p))
        log_graphviz(repo, p, seen)

def cmd_ls_tree(args):
    repo = repo_find()
    assert(repo is not None)

    obj = object_read(repo, object_find(repo, args.object, ty=b'tree'))
    assert(type(obj) is GitTree)

    for entry in obj.entries:
        print('{} {} {}\t{}'.format(
            '0' * (6 - len(entry.mode)) + entry.mode.decode('ascii'),
            object_read(repo, entry.sha).ty.decode('ascii'),
            entry.sha,
            entry.path.decode('ascii')))

def cmd_merge(args):
    raise NotImplementedError()

def cmd_rebase(args):
    raise NotImplementedError()

def cmd_rev_parse(args):
    if args.type:
        ty = args.type.encode()
    repo = repo_find()
    assert(repo is not None)
    print(object_find(repo, args.name, args.type, follow=True))

def cmd_rm(args):
    raise NotImplementedError()

def cmd_show_ref(args):
    repo = repo_find()
    assert(repo is not None)
    refs = ref_list(repo)
    show_ref(repo, refs, prefix='refs')

def show_ref(repo: GitRepo, refs: RefList, with_hash: bool=True, prefix: str=''):
    for k, v in refs.items():
        if type(v) is str:
            print('{}{}{}'.format(
                cast(str, v) + ' ' if with_hash else '',
                prefix + '/' if prefix else '',
                k))
        else:
            show_ref(repo, v, with_hash=with_hash, prefix='{}{}{}'.format(prefix, '/' if prefix else '', k))

def cmd_tag(args):
    repo = repo_find()
    assert(repo is not None)

    if args.name:
        tag_create(args.name,
                   args.object,
                   type='object' if args.create_tag_object else 'ref')
    else:
        refs = ref_list(repo)
        tags = refs['tags']
        assert(type(tags) is not str) # tags ia always a directory
        show_ref(repo, cast(RefList, tags), with_hash=False)

def main():
    args = parse_cli(sys.argv[1:])
    try:
        {
            'add': lambda: cmd_add(args),
            'cat-file': lambda: cmd_cat_file(args),
            'checkout': lambda: cmd_checkout(args),
            'commit': lambda: cmd_commit(args),
            'hash-object': lambda: cmd_hash_object(args),
            'init': lambda: cmd_init(args),
            'log': lambda: cmd_log(args),
            'ls-tree': lambda: cmd_ls_tree(args),
            'merge': lambda: cmd_merge(args),
            'rebase': lambda: cmd_rebase(args),
            'rev-parse': lambda: cmd_rev_parse(args),
            'rm': lambda: cmd_rm(args),
            'show-ref': lambda: cmd_show_ref(args),
            'tag': lambda: cmd_tag(args)
        }[args.command]()
    except KeyError:
        print('invalid command: {}'.format(args.command))

if __name__ == '__main__':
    main()
