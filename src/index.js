import React, { Component } from "react";
import { Theme } from "packard-belle";
import cx from "classnames";
import TaskBar from "./components/TaskBar";
import WindowManager from "./components/WindowManager";
import ProgramProvider from "./contexts/programs";
import SettingsProvider, { SettingsContext } from "./contexts/settings";
import TaskManager from "./components/TaskManager";
import DesktopView from "./components/DesktopView";
import Settings from "./components/Settings";
import CRTOverlay from "./components/tools/CRT";
import ShutDown from "./components/ShutDown/ShutDown";
import Background from "./components/tools/Background";
import "./App.scss";

class Desktop extends Component {
  static contextType = SettingsContext;

  componentDidMount() {
    if (window.innerWidth < 800) {
      this.context.toggleMobile(true);
    }
  }

  render() {
    const { context } = this;
    return (
      <ProgramProvider>
        <Theme
          className={cx("desktop screen", {
            desktopX2: context.scale === 2,
            desktopX1_5: context.scale === 1.5,
            notMobile: !context.isMobile,
            fullScreen: context.fullScreen
          })}
        >
          <Background />
          <DesktopView />
          <TaskBar />
          <WindowManager />
          <TaskManager />
          <Settings />
          <ShutDown />
          {context.crt && <CRTOverlay />}
        </Theme>
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
