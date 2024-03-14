import DataNode from "../classes/data";
import DirNode from "../classes/directory";
import { FileTypes } from "../classes/types";
import { Action, fileSystemReducer, LogStatus, SimulatedFileSystem } from "../filesystem";
import { getFileFromPath, mntHierarchyNested } from "../utils"

describe('fileSystemReducer', () => {
  let state: SimulatedFileSystem;

  describe('basic behaviour', () => {
    beforeEach(() => {
      state = {
        fileHierarchy: new DirNode(mntHierarchyNested),
        logs: {},
      };
    })
    // [x] creates new file
    // [x] fails if file already exists
    // [ ] fails if invalid name format
    it(Action.NEW, () => {
      let newSystem = fileSystemReducer(state, {
        type: Action.NEW,
        value: {
          actionId: 'abc',
          location: '/mnt/c/usr/me',
          newFile: {
            type: FileTypes.DATA,
            data: { text: 'this is the text' },
            name: 'testFile.txt',
          }
        },
      });
      expect(getFileFromPath('/mnt/c/usr/me/testFile.txt', newSystem.fileHierarchy)).toBeTruthy();

      newSystem = fileSystemReducer(state, {
        type: Action.NEW,
        value: {
          actionId: LogStatus.ALREADY_EXISTS,
          location: '/mnt/c/usr/me',
          newFile: {
            type: FileTypes.DATA,
            data: { text: 'this is the text' },
            name: 'testFile.txt',
          }
        },
      });
      expect(newSystem.logs[LogStatus.ALREADY_EXISTS].status).toBe(LogStatus.ALREADY_EXISTS);
      newSystem = fileSystemReducer(state, {
        type: Action.NEW,
        value: {
          actionId: LogStatus.INVALID_FILE_NAME,
          location: '/mnt/c/usr/me',
          newFile: {
            type: FileTypes.DATA,
            data: { text: 'this is the text' },
            name: '$//.txt',
          }
        },
      });
      expect(newSystem.logs[LogStatus.INVALID_FILE_NAME].status).toBe(LogStatus.INVALID_FILE_NAME);
    });
    // [x] copies file
    // [x] fails to copy if duplicate
    // [x] force override on copy
    it(Action.COPY, () => {
      let copySystem = fileSystemReducer(state, {
        type: Action.COPY,
        value: {
          file: '/mnt/c/usr/me/desktop/resume.txt',
          newLocation: '/mnt/c/usr/me',
          actionId: 'abcd',
        },
      });
      expect(getFileFromPath('/mnt/c/usr/me/desktop/resume.txt', copySystem.fileHierarchy)).toBeTruthy();
      expect(getFileFromPath('/mnt/c/usr/me/resume.txt', copySystem.fileHierarchy)).toBeTruthy();
      const failCopy = 'fail-copy';
      copySystem = fileSystemReducer(copySystem, {
        type: Action.COPY,
        value: {
          file: '/mnt/c/usr/me/desktop/resume.txt',
          newLocation: '/mnt/c/usr/me',
          actionId: failCopy,
        },
      });
      expect(copySystem.logs[failCopy].status).toBe(LogStatus.ALREADY_EXISTS);
      const forceCopy  = 'force-copy';
      copySystem = fileSystemReducer(copySystem, {
        type: Action.COPY,
        value: {
          file: '/mnt/c/usr/me/desktop/resume.txt',
          newLocation: '/mnt/c/usr/me',
          actionId: forceCopy,
          force: true,
        },
      });
      expect(copySystem.logs[forceCopy]).not.toBeDefined();
    });
    // [x] delete
    // [x] fails to delete if not exist
    it(Action.DELETE, () => {
      expect(getFileFromPath('/mnt/c/usr/me/desktop/resume.txt', state.fileHierarchy)).toBeTruthy();
      fileSystemReducer(state, {
        type: Action.DELETE,
        value: {
          file: '/mnt/c/usr/me/desktop/resume.txt',
          actionId: 'abcde'
        }
      });
      expect(getFileFromPath('/mnt/c/usr/me/desktop/resume.txt', state.fileHierarchy)).toBeFalsy();
      const actionId = 'delete-no-exist';
      let newState = fileSystemReducer(state, {
        type: Action.DELETE,
        value: {
          file: '/mnt/c/usr/me/desktop/resume.txt',
          actionId,
        }
      });
      expect(newState.logs[actionId].status).toBe(LogStatus.NO_SUCH_FILE);
    });
    // [x] file exists in new directory
    // [x] file no longer exists in source directory
    // [x] path is already in use
    // [ ] fails if invalid name format
    it(Action.MOVE, () => {
      expect(getFileFromPath('/mnt/c/usr/me/desktop/resume.txt', state.fileHierarchy)).toBeTruthy();
      let newState = fileSystemReducer(state, {
        type: Action.MOVE,
        value: {
          file: '/mnt/c/usr/me/desktop/resume.txt',
          newLocation: '/mnt/c/usr/me',
          actionId: 'abcd',
        },
      });
      expect(getFileFromPath('/mnt/c/usr/me/desktop/resume.txt', newState.fileHierarchy)).toBeFalsy();
      expect(getFileFromPath('/mnt/c/usr/me/resume.txt', newState.fileHierarchy)).toBeTruthy();
  
      const actionId = 'move-no-exist';
      newState = fileSystemReducer(newState, {
        type: Action.MOVE,
        value: {
          file: '/mnt/c/usr/me/desktop/resume.txt',
          newLocation: '/mnt/c/usr/me',
          actionId,
        },
      });
      expect(newState.logs[actionId].status).toBe(LogStatus.NO_SUCH_FILE);
      const alreadyExistMove = 'already-exist';
      newState = fileSystemReducer(state, {
        type: Action.MOVE,
        value: {
          file: '/mnt/c/usr/me/desktop/readme.html',
          newLocation: '/mnt/c/usr/me',
          actionId: alreadyExistMove,
        },
      });
      expect(newState.logs[alreadyExistMove].status).toBe(LogStatus.ALREADY_EXISTS);
      newState = fileSystemReducer(state, {
        type: Action.MOVE,
        value: {
          file: '/mnt/c/usr/me/desktop/readme.html',
          newLocation: '/mnt/c/usr//me',
          newName: 'readme.html',
          actionId: LogStatus.INVALID_PATH_NAME,
        },
      });
      expect(newState.logs[LogStatus.INVALID_PATH_NAME].status).toBe(LogStatus.INVALID_PATH_NAME);
    });
    it(Action.UPDATE, () => {
      const newData = 'new data';
      let newState = fileSystemReducer(state, {
        type: Action.UPDATE,
        value: {
          file: '/mnt/c/usr/me/desktop/resume.txt',
          actionId: 'abcd',
          newData: newData
        },
      });
      const data = (getFileFromPath('/mnt/c/usr/me/desktop/resume.txt', newState.fileHierarchy) as DataNode)
      expect(data?.data).toBe(newData);
    });
  });
  describe('readonly behaviour', () => {
    const copyActions = [
      {
        actionId: `${LogStatus.UNAUTHORIZED}-file`,
        file: '/mnt/c/usr/me/readonly.txt',
        newLocation: '/mnt/c/usr',
      },
      {
        actionId: `${LogStatus.UNAUTHORIZED}-directory`,
        file: '/mnt/c/usr/me/readonly/file.txt',
        newLocation: '/mnt/c/usr/me',
      },
      {
        actionId: `${LogStatus.UNAUTHORIZED}-nestedDirectory`,
        file: '/mnt/c/usr/me/readonly/nested/file.txt',
        newLocation: '/mnt/c/usr',
      }
    ]
    beforeAll(() => {
      state = {
        fileHierarchy: new DirNode(mntHierarchyNested),
        logs: {},
      };
      for(let i in copyActions) {
        state = fileSystemReducer(state, {
          type: Action.COPY,
          value: copyActions[i],
        });
      }
    });

    it(Action.NEW, () => {
      let actionId = `${Action.NEW}-${LogStatus.UNAUTHORIZED}`;
      let newSystem = fileSystemReducer(state, {
        type: Action.NEW,
        value: {
          actionId,
          location: '/mnt/c/usr/me/readonly',
          newFile: {
            type: FileTypes.DATA,
            data: { text: 'this is the text' },
            name: 'testFile.txt',
          },
        },
      });

      expect(newSystem.logs[actionId]?.status).toBe(LogStatus.UNAUTHORIZED);

      actionId = `${Action.NEW}-${LogStatus.UNAUTHORIZED}-nested`;
      newSystem = fileSystemReducer(newSystem, {
        type: Action.NEW,
        value: {
          actionId,
          location: '/mnt/c/usr/me/readonly/nested',
          newFile: {
            type: FileTypes.DATA,
            data: { text: 'this is the text' },
            name: 'testFile.txt',
          }
        },
      });
      expect(newSystem.logs[actionId].status).toBe(LogStatus.UNAUTHORIZED);
    });
    it(Action.COPY, () => {
      for (let i of copyActions) {
        const fileName = [...i.file.split('/')].pop()
        const file = getFileFromPath(`${i.newLocation}/${fileName}`, state.fileHierarchy);
        expect(state.logs[i.actionId]).toBeFalsy();
        expect(file).toBeTruthy();
        expect(file?.isReadOnly()).toBe(false);
      }
    });
    it(Action.MOVE, () => {
      const moveActions = [
        { actionId: `${Action.MOVE}-from-file`, file: '/mnt/c/usr/me/readonly.txt', newLocation: '/mnt/c/usr/me/desktop' },
        { actionId: `${Action.MOVE}-from-directory`, file: '/mnt/c/usr/me/readonly/file.txt', newLocation: '/mnt/c/usr/me' },
        { actionId: `${Action.MOVE}-from-nested`, file: '/mnt/c/usr/me/readonly/nested/file.txt', newLocation: '/mnt/c/usr/me/desktop'},
        { actionId: `${Action.MOVE}-to-directory`, file: '/mnt/c/usr/me/desktop/resume.txt', newLocation: '/mnt/c/usr/me/readonly' },
        { actionId: `${Action.MOVE}-to-nested`, file: '/mnt/c/usr/me/desktop/resume.txt', newLocation: '/mnt/c/usr/me/readonly/nested'},
      ]
      let newSystem = state;
      for (let i of moveActions) {
        newSystem = fileSystemReducer(state, {
          type: Action.MOVE,
          value: i,
        });
        expect(newSystem.logs[i.actionId].status).toBe(LogStatus.UNAUTHORIZED);
      }
    });
    // [ ] readonly file
    // [ ] readonly directory
    // [ ] readonly nested directory
    // [ ] file which has been changed since current state [maybe not for this context]
    it(Action.UPDATE, () => {
      const readOnlyFile = ['readonlyfile', '/mnt/c/usr/me/readonly.txt'];
      const readOnlyDir = ['readonlydir', '/mnt/c/usr/me/readonly/file.txt'];
      const readOnlyNested = ['readonlynested', '/mnt/c/usr/me/readonly/nested/file.txt'];
      const actions = [readOnlyFile, readOnlyDir, readOnlyNested]
      let newState = state;
      for (let [actionId, file] of actions) {
        newState = fileSystemReducer(state, {
          type: Action.UPDATE,
          value: {
            file,
            actionId: actionId,
            newData: 'new data here'
          },
        });
        expect(newState.logs[actionId].status).toBe(LogStatus.UNAUTHORIZED);
      }
    });
  })
})