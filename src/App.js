import React, { Component } from "react";
import { Theme, ExplorerView, ExplorerIcon } from "packard-belle";
import cx from "classnames";
import logo from "./logo.svg";
import "./App.css";
import TaskBar from "./components/TaskBar";
import WindowManager from "./components/WindowManager";
import ProgramProvider, { ProgramContext } from "./contexts/programs";
import SettingsProvider, { SettingsContext } from "./contexts/settings";
import TaskManager from "./components/TaskManager";
import DesktopView from "./components/DesktopView";

const testOptions = [
  {
    title: "Test",
    icon: logo,
    onClick: () => {},
    options: [
      {
        title: "Test",
        icon: logo,
        onClick: () => {}
      }
    ]
  },
  {
    title: "Test2",
    icon: logo,
    onClick: () => {}
  },
  {
    title: "Test3",
    icon: logo,
    onClick: () => {}
  },
  {
    title: "Test4",
    icon: logo,
    onClick: () => {}
  }
];

class Desktop extends Component {
  static contextType = SettingsContext;

  render() {
    const { context } = this;
    return (
      <ProgramProvider>
        <Theme className={cx("desktop", { desktopX2: context.scale === 2 })}>
          <DesktopView />
          <TaskBar />
          <WindowManager />
          <TaskManager />
        </Theme>
        <button
          style={{
            right: "0px",
            top: "0px",
            position: "absolute",
            marginBottom: "30px"
          }}
          onClick={context.changeScale}
        >
          changeSettings
        </button>
      </ProgramProvider>
    );
  }
}

const App = () => (
  <SettingsProvider>
    <Desktop />
  </SettingsProvider>
);

// include corner thing if resizable
// body of explorer window needs to fill space

export default App;
