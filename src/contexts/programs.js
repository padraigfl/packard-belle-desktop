import React, { Component, createContext } from "react";
import nanoid from "nanoid";
import startMenuData from "../data/start";
import desktopData from "../data/desktop";
import * as icons from "../icons";
import ExplorerWindow from "../components/ExplorerWindow";

export const ProgramContext = createContext();

const settings = (injectedData = []) => [
  [
    ...injectedData,
    {
      title: "Printers",
      icon: icons.settingsPrinters16,
      Component: ExplorerWindow,
      isDisabled: true
    },
    {
      title: "Folder Options",
      icon: icons.folderOptions16,
      isDisabled: true
    },
    {
      title: "Active Desktop",
      icon: icons.activeDesktop16,
      isDisabled: true
    }
  ],
  {
    title: "Windows Update...",
    icon: icons.windowsUpdate16
  }
];

const startMenu = (injectedData = [], set) => [
  {
    title: "Windows Update",
    icon: icons.windowsUpdate24,
    isDisabled: true
  },
  [
    ...injectedData,
    {
      title: "Settings",
      icon: icons.settings24,
      options: settings(set)
    },
    {
      title: "Help",
      icon: icons.help24,
      options: []
    },
    {
      title: "Run...",
      icon: icons.run24,
      options: []
    }
  ],
  {
    title: "Log Off",
    icon: icons.logOff24,
    isDisabled: true
  },
  {
    title: "Shut Down...",
    icon: icons.shutDown24
  }
];

const sameProgram = a => b => a === b.id;
const notSameProgram = a => b => a !== b.id;

const addIdsToData = data =>
  Array.isArray(data)
    ? data.map(d => {
        if (Array.isArray(d)) {
          return addIdsToData(d);
        }
        return {
          ...d,
          id: nanoid(),
          options: addIdsToData(d.options)
        };
      })
    : undefined;

const desktopWithIds = addIdsToData(desktopData).map(entry => {
  const { onClick, ...data } = entry;
  return {
    ...data,
    onDoubleClick: onClick
  };
});

const initialize = (open, data, doubleClick) =>
  Array.isArray(data)
    ? data.map(d => {
        if (Array.isArray(d)) {
          return initialize(open, d);
        }
        const { onClick, ...nestedData } = d;
        const onClickAction = !d.options
          ? (...params) => {
              if (d.Component) {
                open(d);
              }
              if (d.onClick) {
                d.onClick(...params);
              }
              if (d.onDoubleClick) {
                d.onDoubleClick(...params);
              }
            }
          : undefined;
        return {
          ...nestedData,
          onClick: !doubleClick ? onClickAction : undefined,
          onDoubleClick: doubleClick ? onClick : undefined,
          options: initialize(open, d.options)
        };
      })
    : undefined;

class ProgramProvider extends Component {
  state = {
    startMenu: initialize(
      p => this.open(p),
      addIdsToData(
        startMenu(startMenuData, [
          { title: "Ctrl+Alt+Del", onClick: () => this.toggleTaskManager() },
          {
            title: "Control Panel",
            onClick: () => this.toggleSettings(),
            icon: icons.controlPanel16
          }
        ])
      )
    ),
    desktop: initialize(p => this.open(p), desktopWithIds).map(entry => {
      const { onClick, ...data } = entry;
      return {
        ...data,
        onDoubleClick: onClick
      };
    }),
    quickLaunch: [
      {
        onClick: () => this.minimizeAll(),
        icon: icons.activeDesktop16,
        title: "Display Desktop"
      }
    ],
    activePrograms: [],
    openOrder: [],
    settingsDisplay: false
  };

  toggleTaskManager = () =>
    this.setState(state => ({ taskManager: !state.taskManager }));
  toggleSettings = () =>
    this.setState(state => ({ settingsDisplay: !state.settingsDisplay }));

  isProgramActive = programId =>
    this.state.activePrograms.some(sameProgram(programId));

  exit = programId =>
    this.setState({
      activePrograms: this.state.activePrograms.filter(
        notSameProgram(programId)
      ),
      openOrder: this.state.openOrder.filter(x => x !== programId),
      activeId: null
    });

  moveToTop = programId => {
    const programIndex = this.state.activePrograms.findIndex(
      sameProgram(programId)
    );
    if (programIndex === -1) {
      return;
    }
    this.setState({
      activePrograms: [
        ...this.state.activePrograms.filter(notSameProgram(programId)),
        {
          ...this.state.activePrograms[programIndex],
          minimized: false
        }
      ],
      activeId: programId
    });
  };

  open = program => {
    if (!program.Component) {
      return;
    }
    if (this.isProgramActive(program) && !program.multiWindow) {
      this.moveToTop(program);
      return;
    }
    const newProgram = {
      ...program,
      id: program.multiWindow ? nanoid() : program.id
    };
    this.setState({
      activePrograms: [...this.state.activePrograms, newProgram],
      openOrder: [...this.state.openOrder, newProgram.id],
      activeId: newProgram.id
    });
  };

  close = (program, exit) => {
    if (!this.isProgramActive(program)) {
      return;
    }

    const taskBar = this.state.openOrder.filter(p => p !== program.id);
    this.setState({ openOrder: taskBar });

    if (!program.background || exit) {
      this.exit(program);
    }
  };

  minimize = programId => {
    if (!this.isProgramActive(programId)) {
      return;
    } else {
      const programIndex = this.state.activePrograms.findIndex(
        sameProgram(programId)
      );
      this.setState({
        activePrograms: [
          {
            ...this.state.activePrograms[programIndex],
            minimized: true
          },
          ...this.state.activePrograms.filter(prog => prog.id !== programId)
        ],
        activeId: null
      });
    }
  };
  minimizeAll = () =>
    this.setState(state => ({
      activePrograms: state.activePrograms.map(p => ({
        ...p,
        minimized: true
      })),
      activeId: null
    }));

  render() {
    return (
      <ProgramContext.Provider
        value={{
          ...this.state,
          onOpen: this.open,
          onClose: this.close,
          moveToTop: this.moveToTop,
          toggleTaskManager: this.toggleTaskManager,
          toggleSettings: this.toggleSettings,
          onMinimize: this.minimize
        }}
      >
        {this.props.children}
      </ProgramContext.Provider>
    );
  }
}

export default ProgramProvider;
