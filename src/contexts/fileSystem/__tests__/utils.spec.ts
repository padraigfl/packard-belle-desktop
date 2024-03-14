import { AbstractFileParams } from "../classes/abstract";
import DirNode from "../classes/directory";
import { ValidFileNode } from "../classes/types";
import { mntHierarchyNested, getFileFromPath, deleteFile } from "../utils";

describe('filesystem utils', () => {
  let fileSystem: any;
  describe('cross referencing filesystem class and object interoperability', () => {
    beforeAll(() => {
      fileSystem = new DirNode(mntHierarchyNested, null);
    })
    it('class and object have same keys and values', () => {
      const checkAllChildrenForDifference = (object: AbstractFileParams, chain: string[]): any => {
        let nonMatchFileDir = '';
        const filePath = [...chain, object.name];
        const matchingFile = getFileFromPath(`${filePath.join('/')}` || '/', fileSystem);
        for (let [k, v ] of Object.entries(object)) {
          const currentPath = filePath.join('/');
          if (['name', 'link'].includes(k) && v !== (matchingFile as any)[k]) {
            nonMatchFileDir = currentPath;
          }
          if (k === 'data') {
            if (Object.entries(v).find(([k, v]) => typeof v !== 'object' && v === (matchingFile as any).data[k])) {
              nonMatchFileDir = currentPath;
            };
          }
          if (k === 'contents') {
            for (let content of v) {
              const res = checkAllChildrenForDifference(content, [...filePath]);
              if (res) {
                nonMatchFileDir = currentPath;
                break;
              }
            }
          }
          if (nonMatchFileDir) {
            break;
          }
        }
        return nonMatchFileDir;
      }
      expect(checkAllChildrenForDifference(mntHierarchyNested, [])).toBeFalsy();
    });
  });
  describe('getFileFromPath', () => {
    beforeAll(() => {
      fileSystem = new DirNode(mntHierarchyNested, null);
    })
    it('can get root', () => {
      expect(getFileFromPath('', fileSystem)).toBeTruthy();
    });
    it('absolute path applied to root', () => {
      expect(getFileFromPath('/mnt/c/usr/me/desktop/resume.txt', fileSystem)).toBeTruthy();
    });
    it('get from relative path (i.e. "search current directory"', () => {
      expect(getFileFromPath('usr/me/desktop/resume.txt', getFileFromPath('mnt/c', fileSystem) as DirNode)).toBeTruthy();
    });
    it('get from absolute path applied to nested path (i.e. "search everywhere")', () => {
      const cDrive = getFileFromPath('mnt/c', fileSystem) as DirNode;
      expect(getFileFromPath('/mnt/c/usr/me/desktop/resume.txt', cDrive)).toBeTruthy();
    });
  });
  describe('deleteFile', () => {
    beforeAll(() => {
      fileSystem = new DirNode(mntHierarchyNested, null);
    })
    it('deletes selected file', () => {
      const path = '/mnt/c/usr/me/desktop/readme.html';
      deleteFile(fileSystem, path);
      expect(getFileFromPath(path, fileSystem)).toBeFalsy();
    });
    it('error if attempt root delete', () => {
      const path = '/';
      try {
        deleteFile(fileSystem, path);
      } catch(e: any) {
        expect(e?.message).toEqual('unauthorized');
      }
    });
    it('error if no file', () => {
      const path = '/mnt/c/usr/me/desktop/not-an-actual-file.html';
      try {
        deleteFile(fileSystem, path);
      } catch(e: any) {
        expect(e?.message).toEqual('no-such-file');
      }
    });
  });
});